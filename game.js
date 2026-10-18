import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import {
  getAuth, setPersistence, browserLocalPersistence, onAuthStateChanged,
  signInAnonymously, signInWithEmailAndPassword, signOut
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import {
  getDatabase, ref, onValue, onChildAdded, onChildChanged, onChildRemoved, get, set, update, push,
  runTransaction, serverTimestamp, onDisconnect, query, orderByChild, limitToLast
} from "https://www.gstatic.com/firebasejs/10.12.2/firebase-database.js";
import { CONFIG } from "./config.js";

/*
 * 서버 없는 구조
 * - 각 브라우저가 "자기 뱀"만 계산하고, 머리 위치/길이/점수를 RTDB에 초당 몇 번 올립니다.
 * - 다른 뱀은 받은 머리 좌표를 이어 붙여 몸통을 복원해 그립니다.
 * - 충돌은 부딪힌 본인이 판정(머리가 남의 몸에 닿으면 스스로 탈락 기록)합니다.
 * - 먹이는 gameId 시드로 모두가 같은 위치를 계산하고, 트랜잭션으로 "먼저 먹은 사람"만 인정합니다.
 * - 시간은 Firebase 서버 시각 기준. 누가 나가도 모든 화면이 같은 시각에 끝납니다.
 * - 탭이 백그라운드로 가면 그 뱀은 제자리에 멈춘 장애물이 됩니다.
 */

// ───────────────────────── 설정 ─────────────────────────
const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
const GC = CONFIG.game || {};
const MAX_PLAYERS = Math.max(1, Math.min(20, GC.maxPlayers || 20)); // 규칙(database.rules.json)상 최대 20
const INIT_LEN = GC.initialSnakeLength || 5;
const GRACE_MS = (GC.reconnectGraceSeconds || 60) * 1000;         // 규칙의 60000과 맞춰야 함
const SYNC_MS = 1000 / Math.min(15, Math.max(4, GC.syncRate || 8));
const ARENA_R = GC.arenaRadius || 2200;
const FOOD_N = Math.min(900, GC.foodCount || 350);
const SPEED = 170, BOOST_SPEED = 300, BOOST_COST = 2.5, TURN_RATE = 4.5, UNIT = 14, MAX_SCORE_STEP = 80;
const RETURN_SHIELD_MS = 1500;

const radius = len => 9 + Math.min(16, Math.sqrt(Math.max(1, len)) * 1.1);
const wrap = a => { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; };
const r1 = v => Math.round(v * 10) / 10;
const sleep = ms => new Promise(r => setTimeout(r, ms));
const fmtTime = ms => { const s = Math.max(0, Math.ceil(ms / 1000)); return `${Math.floor(s / 60)}:${String(s % 60).padStart(2, "0")}`; };
const isTouch = matchMedia("(pointer: coarse)").matches || "ontouchstart" in window;

const S = {
  user: null, isAdmin: false, offset: 0, connected: false, ready: { meta: false, players: false },
  meta: null, players: {}, heads: new Map(), drops: new Map(), eaten: {}, natural: [], pending: new Set(),
  me: null, spawning: false, spectator: false, adminOpen: false, fatal: null, kicked: false,
  tabId: (crypto.randomUUID ? crypto.randomUUID() : String(Math.random())), tabClaimed: false,
  lastStatus: null, result: null, overSeen: null, histTried: new Set(), iDied: null,
  fx: [], cam: { x: 0, y: 0, z: 1 }, myHead: null, lb: [], historyLoaded: false,
};
const serverNow = () => Date.now() + S.offset;
const myUid = () => (S.user ? S.user.uid : null);
const myPlayer = () => S.players[myUid()];

function hueOf(uid) {
  const p = S.players[uid];
  if (p && p.slot != null) return Math.round((Number(p.slot) * 137.508 + 15) % 360);
  let h = 0; for (const c of uid || "") h = (h * 31 + c.charCodeAt(0)) % 360;
  return h;
}

// ───────────────────────── 먹이: 시드 기반 결정적 생성 ─────────────────────────
function rng(a) {
  return () => {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function foodAt(i, gen) {
  const r = rng((S.meta.seed ^ Math.imul(i + 1, 0x9E3779B1) ^ Math.imul(gen + 1, 0x85EBCA77)) >>> 0);
  r();
  const a = r() * Math.PI * 2, d = ARENA_R * 0.96 * Math.sqrt(r()), roll = r();
  return { i, gen, x: Math.cos(a) * d, y: Math.sin(a) * d, v: roll < 0.75 ? 1 : roll < 0.95 ? 2 : 3, h: Math.floor(r() * 360) };
}
function rebuildFood() {
  S.natural = S.meta && S.meta.seed != null ? Array.from({ length: FOOD_N }, (_, i) => foodAt(i, S.eaten[i] || 0)) : [];
}

// ───────────────────────── 게임 상태 계산 ─────────────────────────
function inGameHeads() {
  const out = [], gid = S.meta && S.meta.gameId;
  if (!gid) return out;
  for (const [u, h] of S.heads) if (h.data && h.data.g === gid) out.push([u, h]);
  return out;
}
function allDead() {
  const hs = inGameHeads();
  return hs.length > 0 && !S.me && !S.spawning && hs.every(([, h]) => h.data.d);
}
function gameStatus() {
  const m = S.meta;
  if (!m || !m.status || m.status === "waiting" || !m.gameId) return "waiting";
  if (m.status === "finished") return "finished";
  const t = serverNow();
  if (t >= m.endsAt || allDead()) return "finished";
  if (t < m.startedAt) return "countdown";
  return "running";
}

// 공식 순위: 점수 → 길이 → 생존 여부 → 생존 시간 → 먼저 참가한 순
function leaderboard(useLocal) {
  if (!S.meta) return [];
  const t = Math.min(serverNow(), S.meta.endsAt || Infinity);
  const rows = inGameHeads().map(([u, h]) => {
    const d = h.data, p = S.players[u];
    let s = d.s, l = d.l;
    if (useLocal && u === myUid() && S.me) { s = S.me.score; l = S.me.len; }
    const end = d.d ? (d.dt || (p && p.offlineAt) || t) : t;
    return {
      uid: u, nickname: d.n || (p && p.name) || "?", score: s, length: Math.floor(l), alive: !d.d,
      survivalSec: Math.max(0, Math.round((Math.min(end, t) - (d.st || S.meta.startedAt)) / 1000)),
      joinedAt: (p && p.joinedAt) || 0, paused: !!d.p, online: !!p && p.online !== false,
    };
  });
  rows.sort((a, b) => b.score - a.score || b.length - a.length || (b.alive - a.alive) ||
    b.survivalSec - a.survivalSec || a.joinedAt - b.joinedAt || (a.uid < b.uid ? -1 : 1));
  rows.forEach((r, i) => { r.rank = i + 1; });
  return rows;
}

// ───────────────────────── UI 공통 ─────────────────────────
function toast(msg, ms = 2600) {
  const d = document.createElement("div");
  d.textContent = msg;
  $("toast").appendChild(d);
  while ($("toast").children.length > 3) $("toast").firstChild.remove();
  setTimeout(() => d.remove(), ms);
}
function setConn(kind, text) {
  $("conn").className = "conn " + kind;
  $("conn").querySelector("span").textContent = text;
}
const show = (id, on) => $(id).classList.toggle("hidden", !on);

function configError() {
  const f = CONFIG.firebase || {};
  if (!f.apiKey || f.apiKey.startsWith("YOUR") || !f.databaseURL || f.databaseURL.includes("YOUR"))
    return "config.js의 Firebase 설정값을 입력해 주세요.";
  return null;
}

function refreshUI() {
  const st = gameStatus();
  const ready = S.user && S.ready.meta && S.ready.players;
  const joined = !!myPlayer();
  const finishedUnseen = st === "finished" && S.result && S.overSeen !== S.result.gameId;
  let screen = null;
  if (S.adminOpen) screen = "admin";
  else if (S.fatal) screen = "error";
  else if (!ready) screen = "loading";
  else if (finishedUnseen && (joined || S.spectator)) screen = "over";
  else if (!joined && !S.spectator) screen = "join";
  else if (st === "waiting") screen = "lobby";
  for (const n of ["loading", "error", "join", "lobby", "over", "admin"]) show("screen-" + n, screen === n);

  const playing = ready && st !== "waiting";
  show("hud", playing); show("board", playing); show("minimap", playing);
  show("hud-me", joined);
  show("btn-join-late", S.spectator && !joined && (st === "running" || st === "countdown"));
  show("boost", isTouch && !!S.me && st === "running" && !screen);
  show("admin-panel", S.isAdmin && playing && !screen);
  show("ap-end", st === "running" || st === "countdown");
  show("ap-reset", st === "finished");
  show("countdown", st === "countdown" && !screen);

  const row = S.lb.find(r => r.uid === myUid());
  const dead = st === "running" && joined && !S.me && S.meta && S.iDied === S.meta.gameId;
  show("dead-banner", dead && !screen);
  if (dead) $("dead-banner").innerHTML = `<b>탈락했습니다</b> · ${row ? `${row.score}점, 현재 ${row.rank}위` : ""} · 관전 중`;
  const paused = S.me && S.me.paused;
  if (paused) setConn("wait", "자리 비움");

  if (screen === "join") {
    $("join-sub").textContent = st === "running" || st === "countdown"
      ? "게임이 진행 중입니다. 참가하면 다른 뱀과 먼 곳에서 바로 시작합니다."
      : "먹이를 먹고 커지세요. 다른 뱀의 몸에 머리가 닿으면 탈락합니다.";
    loadHistory();
  }
  if (screen === "lobby") renderLobby();
  if (screen === "error") {
    $("btn-retry").textContent = S.kicked ? "이 탭에서 계속하기" : "다시 시도";
  }
}

function fatal(msg) { S.fatal = msg; $("error-text").textContent = msg; refreshUI(); }

// ───────────────────────── Firebase 연결 ─────────────────────────
let auth = null, db = null, listening = false;
const cfgErr = configError();
if (cfgErr) {
  fatal(cfgErr);
  $("btn-retry").classList.add("hidden");
} else {
  const app = initializeApp(CONFIG.firebase);
  auth = getAuth(app);
  db = getDatabase(app);
  setPersistence(auth, browserLocalPersistence).catch(() => {});
  onAuthStateChanged(auth, onUser);
}
const R = p => ref(db, "game/current/" + p);

function onUser(user) {
  if (!user) {
    signInAnonymously(auth).catch(e => fatal("익명 로그인에 실패했습니다. Firebase 콘솔에서 익명 로그인을 켜 주세요. (" + e.code + ")"));
    return;
  }
  const changed = !S.user || S.user.uid !== user.uid;
  S.user = user;
  $("whoami").textContent = user.isAnonymous ? "게스트(익명)로 접속" : `관리자 계정: ${user.email}`;
  show("btn-admin-open", user.isAnonymous); show("btn-admin-open2", user.isAnonymous); show("btn-logout", !user.isAnonymous);
  if (changed) {
    S.me = null; S.tabClaimed = false; S.isAdmin = false; S.spectator = false; S.iDied = null;
    get(ref(db, "admins/" + user.uid)).then(s => {
      S.isAdmin = s.val() === true;
      if (!S.isAdmin && !user.isAnonymous) toast("이 계정은 관리자로 등록되어 있지 않습니다. 안내서의 관리자 등록 방법을 확인하세요.", 5000);
      refreshUI();
    }).catch(() => {});
  }
  if (!listening) { listening = true; listen(); }
  else { claimPresence(); maybeSpawn(); }
  refreshUI();
}

function listen() {
  onValue(ref(db, ".info/serverTimeOffset"), s => { S.offset = s.val() || 0; });
  onValue(ref(db, ".info/connected"), s => {
    S.connected = s.val() === true;
    setConn(S.connected ? "ok" : "wait", S.connected ? "연결됨" : "재연결 중…");
    if (S.connected) { S.tabClaimed = false; if (!S.kicked) claimPresence(); }
  });
  onValue(R("meta"), s => applyMeta(s.val()),
    e => fatal("게임 데이터를 읽지 못했습니다. Realtime Database 규칙을 확인하세요. (" + e.code + ")"));
  onValue(R("players"), s => applyPlayers(s.val() || {}));
  onChildAdded(R("heads"), s => applyHead(s.key, s.val()));
  onChildChanged(R("heads"), s => applyHead(s.key, s.val()));
  onChildRemoved(R("heads"), s => { S.heads.delete(s.key); });
  onChildAdded(R("drops"), s => { S.drops.set(s.key, s.val()); });
  onChildRemoved(R("drops"), s => { S.drops.delete(s.key); S.pending.delete("d" + s.key); });
  const onEaten = s => {
    const i = Number(s.key), gen = s.val();
    S.eaten[i] = gen;
    if (S.meta && S.meta.seed != null && i < FOOD_N) S.natural[i] = foodAt(i, gen);
    S.pending.delete("n" + i);
  };
  onChildAdded(R("eaten"), onEaten);
  onChildChanged(R("eaten"), onEaten);
  onChildRemoved(R("eaten"), s => {
    const i = Number(s.key);
    delete S.eaten[i];
    if (S.meta && S.meta.seed != null && i < FOOD_N) S.natural[i] = foodAt(i, 0);
  });
}

// 접속 상태(online/offlineAt)와 "이 탭이 조작 중" 표시
function claimPresence() {
  const u = myUid();
  if (!db || !S.connected || !u || !S.players[u] || S.kicked) return;
  const r = R("players/" + u);
  onDisconnect(r).update({ online: false, offlineAt: serverTimestamp() }).catch(() => {});
  S.tabClaimed = true;
  update(r, { online: true, tab: S.tabId }).catch(() => {});
}

function applyPlayers(v) {
  S.players = v; S.ready.players = true;
  const mine = v[myUid()];
  if (mine) {
    if (!S.tabClaimed && !S.kicked) claimPresence();
    else if (S.tabClaimed && mine.tab && mine.tab !== S.tabId && !S.kicked) {
      S.kicked = true; S.me = null; S.tabClaimed = false;
      fatal("다른 탭(또는 기기)에서 같은 계정으로 접속해 이 화면은 멈췄습니다.");
    }
    maybeSpawn();
  }
  refreshUI();
}

function applyMeta(m) {
  const prevId = S.meta && S.meta.gameId;
  S.meta = m; S.ready.meta = true;
  if (((m && m.gameId) || null) !== (prevId || null)) {
    S.me = null; S.pending.clear(); S.iDied = null; S.result = null; S.lb = [];
    for (const [u, h] of S.heads) if (!h.data || !m || h.data.g !== m.gameId) S.heads.delete(u);
    rebuildFood();
  }
  maybeSpawn();
  refreshUI();
}

// 다른 플레이어의 머리 갱신 → 몸통 이어 붙이기
function applyHead(u, v) {
  if (!v) return;
  let h = S.heads.get(u);
  const t = performance.now();
  if (!h) { h = { pts: [], odo: 0, t, data: null, bodyReq: false }; S.heads.set(u, h); }
  if (h.data && h.data.g !== v.g) { h.pts = []; h.bodyReq = false; }
  const wasDead = !!(h.data && h.data.d && h.data.g === v.g);
  h.data = v;
  if (v.d) {
    if (!wasDead && h.pts.length && S.meta && v.g === S.meta.gameId) onDeathSeen(u, h, v);
    h.pts = [];
    return;
  }
  if (u === myUid()) return; // 내 뱀은 로컬 상태로 그림
  const p0 = h.pts[0];
  if (!p0 || p0[0] !== v.x || p0[1] !== v.y) {
    if (p0) h.odo += Math.hypot(v.x - p0[0], v.y - p0[1]);
    h.pts.unshift([v.x, v.y]);
    h.t = t;
    trimPts(h.pts, v.l * UNIT);
  }
  if (!h.bodyReq && S.meta && v.g === S.meta.gameId) {
    h.bodyReq = true; // 처음 본 뱀은 저장된 몸통을 한 번만 읽어 옴
    get(R("bodies/" + u)).then(s => {
      const b = s.val();
      if (!b || b.g !== v.g || !h.data || h.data.d) return;
      const body = decode(b.p);
      if (body.length < 2) return;
      h.pts = h.pts.concat(body);
      trimPts(h.pts, h.data.l * UNIT);
    }).catch(() => {});
  }
}

function onDeathSeen(u, h, v) {
  const p0 = h.pts[0];
  S.fx.push({ x: p0[0], y: p0[1], h: hueOf(u), t: performance.now() });
  const victim = v.n || "?";
  const killer = v.k ? (S.heads.get(v.k) && S.heads.get(v.k).data && S.heads.get(v.k).data.n) || (S.players[v.k] && S.players[v.k].name) : null;
  if (v.k === myUid()) toast(`${victim} 처치!`);
  else if (killer) toast(`${killer} → ${victim} 처치`, 2000);
  else toast(`${victim} 연결 시간 초과로 탈락`, 2000);
}

// ───────────────────────── 몸통 인코딩 ─────────────────────────
function trimPts(pts, maxLen) {
  let acc = 0;
  for (let i = 1; i < pts.length; i++) {
    const a = pts[i - 1], b = pts[i], d = Math.hypot(b[0] - a[0], b[1] - a[1]);
    if (acc + d >= maxLen) {
      const k = d > 0 ? (maxLen - acc) / d : 0;
      pts.length = i + 1;
      pts[i] = [a[0] + (b[0] - a[0]) * k, a[1] + (b[1] - a[1]) * k];
      return;
    }
    acc += d;
  }
}
function encode(pts, len) {
  const step = Math.max(10, (len * UNIT) / 1500);
  const out = [];
  let last = null;
  pts.forEach((p, i) => {
    if (!last || i === pts.length - 1 || Math.hypot(p[0] - last[0], p[1] - last[1]) >= step) {
      out.push(Math.round(p[0]) + "," + Math.round(p[1])); last = p;
    }
  });
  return out.join(";");
}
function decode(s) {
  if (typeof s !== "string" || !s) return [];
  return s.split(";").map(x => x.split(",").map(Number)).filter(a => a.length === 2 && isFinite(a[0]) && isFinite(a[1]));
}
// 몸통 길이를 따라 같은 간격으로 count개 지점
function sampleAlong(pts, count) {
  if (pts.length < 2) return Array.from({ length: count }, () => pts[0]);
  const seg = [];
  let total = 0;
  for (let i = 1; i < pts.length; i++) { const d = Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]); seg.push(d); total += d; }
  const out = [];
  for (let n = 0; n < count; n++) {
    let want = total * (count === 1 ? 0 : n / (count - 1)), i = 0;
    while (i < seg.length - 1 && want > seg[i]) { want -= seg[i]; i++; }
    const k = seg[i] ? Math.min(1, want / seg[i]) : 0, a = pts[i], b = pts[i + 1];
    out.push([a[0] + (b[0] - a[0]) * k, a[1] + (b[1] - a[1]) * k]);
  }
  return out;
}
function line(x, y, a, len) {
  const pts = [], total = len * UNIT;
  for (let d = 0; d <= total; d += 6) pts.push([x - Math.cos(a) * d, y - Math.sin(a) * d]);
  return pts;
}

// ───────────────────────── 내 뱀 생성 / 복구 ─────────────────────────
function makeMe(pts, angle, len, score, st) {
  return {
    pts, angle, target: angle, len, score, sentScore: score, st, alive: true, boost: false, boostAcc: 0,
    dropBuf: [], odo: 0, paused: false, invulnUntil: 0, lastHead: 0, lastBody: performance.now(),
  };
}

function findSpawn() {
  let best = null, bestD = -1;
  for (let t = 0; t < 40; t++) {
    const a = Math.random() * Math.PI * 2, r = ARENA_R * 0.75 * Math.sqrt(Math.random());
    const x = Math.cos(a) * r, y = Math.sin(a) * r;
    let d = Infinity;
    for (const [u, h] of S.heads) {
      if (u === myUid() || !h.data || h.data.d) continue;
      d = Math.min(d, Math.hypot(h.data.x - x, h.data.y - y));
      for (let i = 0; i < h.pts.length; i += 3) d = Math.min(d, Math.hypot(h.pts[i][0] - x, h.pts[i][1] - y));
    }
    if (d > bestD) { bestD = d; best = { x, y, a: Math.atan2(-y, -x) }; }
    if (d > 600) break;
  }
  return best;
}

async function maybeSpawn() {
  const st = gameStatus(), u = myUid();
  if (S.me || S.spawning || S.kicked || !u || !myPlayer() || !(st === "running" || st === "countdown")) return;
  const gid = S.meta.gameId;
  if (S.iDied === gid) return;
  S.spawning = true;
  try {
    const [hs, bs] = await Promise.all([get(R("heads/" + u)), get(R("bodies/" + u))]);
    if (!S.meta || S.meta.gameId !== gid || S.me || S.kicked) return;
    const h = hs.val(), b = bs.val();
    if (h && h.g === gid) {
      if (h.d) { S.iDied = gid; return; }
      // 새로고침 복구: 저장된 몸통 + 마지막 머리 위치
      let pts = b && b.g === gid ? decode(b.p) : [];
      if (pts.length < 2) pts = line(h.x, h.y, h.a || 0, h.l);
      else if (Math.hypot(pts[0][0] - h.x, pts[0][1] - h.y) > 1) pts.unshift([h.x, h.y]);
      S.me = makeMe(pts, h.a || 0, h.l, h.s, h.st || S.meta.startedAt);
      S.me.invulnUntil = serverNow() + RETURN_SHIELD_MS;
      toast("진행 중이던 게임으로 돌아왔습니다");
    } else {
      const fixed = S.meta.spawns && S.meta.spawns[u];
      const sp = fixed || findSpawn();
      S.me = makeMe(line(sp.x, sp.y, sp.a, INIT_LEN), sp.a, INIT_LEN, 0, Math.max(serverNow(), S.meta.startedAt));
      if (!fixed) S.me.invulnUntil = serverNow() + RETURN_SHIELD_MS;
      writeHead(); writeBody();
    }
  } catch (e) {
    console.warn("spawn", e);
  } finally {
    S.spawning = false; refreshUI();
  }
}

// ───────────────────────── 내 상태 쓰기 ─────────────────────────
function headData(m) {
  const s = Math.min(m.score, m.sentScore + MAX_SCORE_STEP); // 규칙상 한 번에 +80까지만 허용
  m.sentScore = s;
  return {
    g: S.meta.gameId, n: (myPlayer() && myPlayer().name) || "?", x: r1(m.pts[0][0]), y: r1(m.pts[0][1]),
    a: Math.round(m.angle * 100) / 100, l: r1(m.len), s, b: m.boost ? 1 : 0, p: m.paused ? 1 : 0, d: false, st: m.st,
  };
}
function writeHead() {
  const m = S.me;
  if (!m || S.kicked || !S.meta) return;
  m.lastHead = performance.now();
  set(R("heads/" + myUid()), headData(m)).catch(() => {});
}
function writeBody() {
  const m = S.me;
  if (!m || S.kicked || !S.meta) return;
  m.lastBody = performance.now();
  set(R("bodies/" + myUid()), { g: S.meta.gameId, a: Math.round(m.angle * 100) / 100, p: encode(m.pts, m.len) }).catch(() => {});
}
function flushDrops() {
  const m = S.me;
  if (!m || !m.dropBuf.length || gameStatus() !== "running") return;
  const up = {};
  for (const d of m.dropBuf.splice(0)) up["drops/" + push(R("drops")).key] = d;
  update(R(""), up).catch(() => {});
}

function die(killerUid) {
  const m = S.me;
  if (!m) return;
  S.me = null; S.iDied = S.meta.gameId;
  const up = {};
  up["heads/" + myUid()] = { ...headData(m), d: true, k: killerUid || null, dt: serverTimestamp() };
  // 몸통 → 먹이 (전체 가치 ≈ 길이의 1.2배)
  const count = Math.max(4, Math.min(40, Math.round(m.len / 2)));
  const each = Math.max(1, Math.min(5, Math.round((m.len * 1.2) / count)));
  const hue = hueOf(myUid());
  for (const [x, y] of sampleAlong(m.pts, count)) {
    up["drops/" + push(R("drops")).key] = { x: r1(x + (Math.random() - 0.5) * 14), y: r1(y + (Math.random() - 0.5) * 14), v: each, h: hue };
  }
  update(R(""), up).catch(() => set(R("heads/" + myUid()), up["heads/" + myUid()]).catch(() => {}));
  S.fx.push({ x: m.pts[0][0], y: m.pts[0][1], h: hue, t: performance.now() });
  const k = killerUid && S.heads.get(killerUid);
  toast(k && k.data ? `${k.data.n}에게 부딪혀 탈락했습니다` : "탈락했습니다", 4000);
  refreshUI();
}

// ───────────────────────── 먹이 먹기 (트랜잭션) ─────────────────────────
function eatNatural(f) {
  const gid = S.meta.gameId;
  S.pending.add("n" + f.i);
  runTransaction(R("eaten/" + f.i), cur => ((cur || 0) === f.gen ? f.gen + 1 : undefined))
    .then(r => { if (r.committed && S.me && S.meta && S.meta.gameId === gid) { S.me.score += f.v; S.me.len += f.v * 0.5; } })
    .catch(() => {})
    .finally(() => S.pending.delete("n" + f.i));
}
function eatDrop(k, f) {
  const gid = S.meta.gameId;
  S.pending.add("d" + k);
  runTransaction(R("drops/" + k), cur => (cur ? null : undefined))
    .then(r => { if (r.committed && S.me && S.meta && S.meta.gameId === gid) { S.me.score += f.v; S.me.len += f.v * 0.5; } })
    .catch(() => { S.pending.delete("d" + k); });
}

// ───────────────────────── 시뮬레이션 (내 뱀만) ─────────────────────────
function segDist2(px, py, a, b) {
  const vx = b[0] - a[0], vy = b[1] - a[1], wx = px - a[0], wy = py - a[1];
  const l2 = vx * vx + vy * vy;
  const t = l2 ? Math.max(0, Math.min(1, (wx * vx + wy * vy) / l2)) : 0;
  const dx = wx - vx * t, dy = wy - vy * t;
  return dx * dx + dy * dy;
}
function hits(px, py, pts, lim) {
  const l2 = lim * lim;
  if (pts.length === 1) { const dx = pts[0][0] - px, dy = pts[0][1] - py; return dx * dx + dy * dy < l2; }
  for (let i = 1; i < pts.length; i++) if (segDist2(px, py, pts[i - 1], pts[i]) < l2) return true;
  return false;
}

function simulate(dt) {
  const m = S.me;
  if (I.mode === "mouse" && I.mouse && S.myHead) I.angle = Math.atan2(I.mouse.y - S.myHead[1], I.mouse.x - S.myHead[0]);
  m.target = I.angle;
  m.boost = I.mouseBoost || I.keyBoost || I.btnBoost || I.boostTouch != null;
  const diff = wrap(m.target - m.angle), mt = TURN_RATE * dt;
  m.angle = wrap(m.angle + Math.max(-mt, Math.min(mt, diff)));
  const boosting = m.boost && m.len > INIT_LEN + 2;
  const sp = boosting ? BOOST_SPEED : SPEED;
  let x = m.pts[0][0] + Math.cos(m.angle) * sp * dt, y = m.pts[0][1] + Math.sin(m.angle) * sp * dt;
  const lim = ARENA_R - radius(m.len), dist = Math.hypot(x, y);
  if (dist > lim) { x = x / dist * lim; y = y / dist * lim; m.angle = m.target = Math.atan2(-y, -x); I.angle = m.angle; }
  m.odo += sp * dt;
  if (m.pts.length > 1 && Math.hypot(m.pts[0][0] - m.pts[1][0], m.pts[0][1] - m.pts[1][1]) < 5) m.pts[0] = [x, y];
  else m.pts.unshift([x, y]);
  if (boosting) {
    m.boostAcc += BOOST_COST * dt;
    while (m.boostAcc >= 1) {
      m.boostAcc -= 1; m.len -= 1;
      const tail = m.pts[m.pts.length - 1];
      m.dropBuf.push({ x: r1(tail[0]), y: r1(tail[1]), v: 1, h: hueOf(myUid()) });
    }
  } else m.boostAcc = 0;
  trimPts(m.pts, m.len * UNIT);

  // 먹이
  const [hx, hy] = m.pts[0], rr = radius(m.len) + 10, rr2 = rr * rr;
  for (const f of S.natural) {
    const dx = f.x - hx, dy = f.y - hy;
    if (dx * dx + dy * dy < rr2 && !S.pending.has("n" + f.i)) eatNatural(f);
  }
  for (const [k, f] of S.drops) {
    const dx = f.x - hx, dy = f.y - hy;
    if (dx * dx + dy * dy < rr2 && !S.pending.has("d" + k)) eatDrop(k, f);
  }

  // 충돌: 내 머리가 다른 뱀(멈춘 뱀 포함)의 몸에 닿으면 탈락. 자기 몸과는 충돌하지 않음.
  if (serverNow() > m.invulnUntil) {
    const myR = radius(m.len);
    for (const [u, h] of S.heads) {
      if (u === myUid() || !h.data || h.data.d || h.data.g !== S.meta.gameId || !h.pts.length) continue;
      const lim2 = radius(h.data.l) + myR * 0.5;
      if (hits(hx, hy, h.pts, lim2)) { die(u); return; }
    }
  }

  const now = performance.now();
  if (now - m.lastHead >= SYNC_MS) writeHead();
  if (now - m.lastBody >= 2000) writeBody();
}

setInterval(flushDrops, 500);

// 연결이 끊긴 뒤 유예 시간이 지난 플레이어 탈락 처리 (누구든 기록 가능, 규칙이 시간 검증)
setInterval(() => {
  if (gameStatus() !== "running") return;
  const t = serverNow();
  for (const [u, h] of S.heads) {
    if (u === myUid() || !h.data || h.data.d || h.data.g !== S.meta.gameId || h.toSent) continue;
    const p = S.players[u];
    if (p && p.online === false && p.offlineAt && t > p.offlineAt + GRACE_MS + 1500) {
      h.toSent = true;
      set(R(`heads/${u}/d`), true).catch(() => { h.toSent = false; });
    }
  }
}, 2000);

// ───────────────────────── 상태 전환 / 결과 ─────────────────────────
function onStatus(st, prev) {
  if (st === "running" && prev === "countdown") toast("시작!");
  if (st === "running" || st === "countdown") maybeSpawn();
  if (st === "finished") {
    if (S.me) { S.me.paused = false; writeHead(); }
    if (S.meta && S.meta.gameId) finalize(S.meta.gameId);
  }
  refreshUI();
}

async function finalize(gid) {
  if (S.histTried.has(gid)) return;
  S.histTried.add(gid);
  await sleep(2500); // 마지막 점수 쓰기가 도착할 시간
  if (!S.meta || S.meta.gameId !== gid) return;
  let result = null;
  try { const s = await get(ref(db, "game/history/" + gid)); if (s.exists()) result = s.val(); } catch {}
  if (!result) {
    const lb = leaderboard(false).map(({ joinedAt, paused, online, ...r }) => r);
    result = {
      gameId: gid, startedAt: S.meta.startedAt, endedAt: Math.min(serverNow(), S.meta.endsAt),
      winnerUid: lb[0] ? lb[0].uid : null, winnerName: lb[0] ? lb[0].nickname : null, finalLeaderboard: lb,
    };
    if (lb.length) {
      try {
        const r = await runTransaction(ref(db, "game/history/" + gid), cur => (cur ? undefined : result));
        if (r.snapshot.exists()) result = r.snapshot.val(); // 다른 사람이 먼저 저장했다면 그 결과 사용
      } catch {}
    }
  }
  if (S.meta && S.meta.status === "running" && serverNow() > S.meta.endsAt)
    set(R("meta/status"), "finished").catch(() => {});
  if (!S.meta || S.meta.gameId !== gid) return;
  S.result = result;
  renderResult();
  refreshUI();
}

// ───────────────────────── 대기실 / 순위표 / 결과 렌더 ─────────────────────────
function renderLobby() {
  const u = myUid();
  const list = Object.entries(S.players).sort((a, b) => Number(a[1].slot) - Number(b[1].slot));
  $("lobby-count").textContent = `${list.length} / ${MAX_PLAYERS}명`;
  $("lobby-sub").textContent = S.isAdmin
    ? "참가자가 모이면 게임을 시작하세요. 시작 후에는 관리자도 똑같이 플레이합니다."
    : myPlayer() ? "관리자가 게임을 시작할 때까지 기다려 주세요." : "관전 중입니다.";
  $("lobby-list").innerHTML = list.map(([id, p]) => `
    <li class="${id === u ? "me" : ""} ${p.online === false ? "off" : ""}">
      <span class="dot" style="background:hsl(${hueOf(id)} 80% 55%)"></span>
      <span class="nm">${esc(p.name)}</span>
      ${id === u ? '<span class="tag">나</span>' : ""}
      ${p.online === false ? '<span class="tag">끊김</span>' : ""}
    </li>`).join("") || '<li class="off"><span class="nm">아직 참가자가 없습니다</span></li>';
  show("admin-lobby", S.isAdmin);
}

let boardRows = new Map();
function renderBoard() {
  const list = $("board-list");
  const before = new Map();
  for (const [id, el] of boardRows) before.set(id, el.getBoundingClientRect().top);
  const next = new Map();
  for (const r of S.lb) {
    let el = boardRows.get(r.uid);
    if (!el) el = document.createElement("li");
    el.className = (r.alive ? "" : "dead ") + (r.uid === myUid() ? "me" : "");
    const note = r.paused ? " · 자리 비움" : r.online === false ? " · 끊김" : "";
    el.innerHTML = `<span class="rk">${r.rank}</span>
      <span class="nm"><i style="background:hsl(${hueOf(r.uid)} 80% 55%)"></i><b>${esc(r.nickname)}</b></span>
      <span class="sc">${r.score}<small>길이 ${r.length}${note}</small></span>`;
    list.appendChild(el);
    next.set(r.uid, el);
  }
  for (const [id, el] of boardRows) if (!next.has(id)) el.remove();
  boardRows = next;
  for (const [id, el] of next) { // FLIP: 순위 변동 애니메이션
    const top = before.get(id);
    if (top == null) continue;
    const dy = top - el.getBoundingClientRect().top;
    if (!dy) continue;
    el.style.transition = "none";
    el.style.transform = `translateY(${dy}px)`;
    requestAnimationFrame(() => { el.style.transition = "transform .35s ease"; el.style.transform = ""; });
  }
  $("board-count").textContent = `${S.lb.filter(r => r.alive).length}/${S.lb.length} 생존`;
  const mine = S.lb.find(r => r.uid === myUid());
  $("my-rank").textContent = mine ? mine.rank : "-";
  if (mine && !S.me) { $("my-score").textContent = mine.score; $("my-len").textContent = mine.length; }
}

function renderResult() {
  const R0 = S.result;
  if (!R0) return;
  const lb = Object.values(R0.finalLeaderboard || {});
  $("winner").textContent = R0.winnerName ? `우승: ${R0.winnerName} (${lb[0] ? lb[0].score : 0}점)` : "참가자가 없습니다";
  $("result-table").querySelector("tbody").innerHTML = lb.map(r => `
    <tr class="${r.uid === myUid() ? "me" : ""}">
      <td>${r.rank}</td><td class="nm">${esc(r.nickname)}</td><td>${r.score}</td><td>${r.length}</td>
      <td>${fmtTime(r.survivalSec * 1000)}</td><td>${r.alive ? "생존" : "탈락"}</td>
    </tr>`).join("");
  show("btn-reset", S.isAdmin);
}

async function loadHistory() {
  if (S.historyLoaded || !db) return;
  S.historyLoaded = true;
  try {
    const snap = await get(query(ref(db, "game/history"), orderByChild("endedAt"), limitToLast(5)));
    const rows = [];
    snap.forEach(c => { rows.push(c.val()); });
    rows.sort((a, b) => b.endedAt - a.endedAt);
    if (!rows.length) return;
    $("history").innerHTML = "<h4>최근 게임</h4>" + rows.map(r => {
      const d = new Date(r.endedAt);
      return `<div><span>${d.getMonth() + 1}/${d.getDate()} ${String(d.getHours()).padStart(2, "0")}:${String(d.getMinutes()).padStart(2, "0")}</span>
        <span>우승 ${esc(r.winnerName || "-")}</span></div>`;
    }).join("");
  } catch { /* 기록 조회 실패는 게임에 영향 없음 */ }
}

// 순위표 갱신(0.5초마다)
setInterval(() => {
  const st = gameStatus();
  if (st !== "waiting" && S.meta) {
    S.lb = st === "finished" && S.result ? Object.values(S.result.finalLeaderboard || {}) : leaderboard(true);
    renderBoard();
  }
  if (st === "running" && !S.me) maybeSpawn();
  refreshUI();
}, 500);

// ───────────────────────── 참가 / 관리자 ─────────────────────────
async function joinGame(name) {
  const u = myUid();
  if (S.players[u]) { // 이미 참가 중 → 게임 전이면 닉네임만 변경
    if (gameStatus() === "waiting") await update(R("players/" + u), { name }).catch(() => {});
    S.spectator = false; claimPresence(); maybeSpawn(); refreshUI();
    return;
  }
  const taken = new Set(Object.values(S.players).map(p => String(p.slot)));
  for (let i = 0; i < MAX_PLAYERS; i++) {
    if (taken.has(String(i))) continue;
    try {
      await update(R(""), {
        ["slots/" + i]: u,
        ["players/" + u]: { name, slot: String(i), joinedAt: serverTimestamp(), online: true, tab: S.tabId },
      });
      try { localStorage.setItem("snake-nickname", name); } catch {}
      S.spectator = false; S.tabClaimed = false;
      claimPresence(); maybeSpawn(); refreshUI();
      return;
    } catch { /* 그 자리를 다른 사람이 먼저 차지함 → 다음 자리 */ }
  }
  S.spectator = true;
  toast(`정원(${MAX_PLAYERS}명)이 가득 찼습니다. 관전 모드로 들어갑니다.`, 4000);
  refreshUI();
}

function offlineRemovals() {
  const up = {};
  for (const [id, p] of Object.entries(S.players)) {
    if (p.online === false) { up["players/" + id] = null; up["slots/" + p.slot] = null; }
  }
  return up;
}

async function adminStart(duration) {
  const roster = Object.entries(S.players).filter(([, p]) => p.online !== false)
    .sort((a, b) => Number(a[1].slot) - Number(b[1].slot)).slice(0, MAX_PLAYERS);
  if (!roster.length) throw new Error("참가자가 없습니다. 닉네임을 입력해 먼저 참가하세요.");
  const dur = Math.max(30, Math.min(3600, Number(duration) || GC.initialGameDurationSeconds || 300));
  const startedAt = Math.round(serverNow()) + 3000; // 3초 카운트다운
  const spawns = {};
  roster.forEach(([id], i) => {
    const a = (i / roster.length) * Math.PI * 2, r = ARENA_R * 0.55;
    spawns[id] = { x: r1(Math.cos(a) * r), y: r1(Math.sin(a) * r), a: Math.round((a + Math.PI / 2) * 100) / 100 };
  });
  const gameId = "g" + Date.now().toString(36) + Math.random().toString(36).slice(2, 5);
  await update(R(""), {
    ...offlineRemovals(),
    meta: { gameId, status: "running", startedAt, endsAt: startedAt + dur * 1000, durationSec: dur, seed: (Math.random() * 2 ** 31) | 0, spawns },
    heads: null, bodies: null, drops: null, eaten: null,
  });
}
async function adminReset() {
  await update(R(""), { ...offlineRemovals(), meta: { status: "waiting" }, heads: null, bodies: null, drops: null, eaten: null });
}

async function adminCmd(cmd, btn) {
  if (cmd === "end" && !confirm("진행 중인 게임을 지금 종료할까요? 현재 순위로 결과가 확정됩니다.")) return;
  if (cmd === "restart" && !confirm("현재 게임을 종료하고 새 게임을 바로 시작할까요?")) return;
  const duration = Number($("duration").value) || GC.initialGameDurationSeconds;
  if (btn) btn.disabled = true;
  try {
    if (cmd === "start") await adminStart(duration);
    else if (cmd === "end") await update(R("meta"), { endsAt: serverTimestamp() });
    else if (cmd === "reset") await adminReset();
    else if (cmd === "clean") { await update(R(""), offlineRemovals()); toast("끊긴 참가자를 정리했습니다."); }
    else if (cmd === "restart") {
      const st = gameStatus();
      if (st === "running" || st === "countdown") {
        await update(R("meta"), { endsAt: serverTimestamp() });
        toast("결과를 저장한 뒤 새 게임을 시작합니다…");
        await sleep(3500);
      }
      await adminStart(duration);
    }
  } catch (e) {
    toast(e && e.code === "PERMISSION_DENIED" ? "관리자 권한이 없습니다." : (e && e.message) || "처리하지 못했습니다.", 4000);
  } finally {
    if (btn) btn.disabled = false;
  }
}

// ───────────────────────── 버튼 / 폼 ─────────────────────────
try { $("nickname").value = localStorage.getItem("snake-nickname") || ""; } catch {}
$("join-form").onsubmit = e => {
  e.preventDefault();
  const name = $("nickname").value.normalize("NFC").replace(/\s+/g, " ").trim();
  $("join-error").textContent = "";
  if (!name || name.length > 12) { $("join-error").textContent = "닉네임은 1~12자로 입력하세요."; return; }
  if (!/^[\p{L}\p{N} _\-.]+$/u.test(name)) { $("join-error").textContent = "한글·영문·숫자·공백·_-. 만 사용할 수 있습니다."; return; }
  if (!S.connected) { $("join-error").textContent = "연결 중입니다. 잠시 후 다시 시도하세요."; return; }
  joinGame(name).catch(() => { $("join-error").textContent = "참가하지 못했습니다. 다시 시도하세요."; });
};
$("btn-spectate").onclick = () => { S.spectator = true; refreshUI(); };
$("btn-join-late").onclick = () => { S.spectator = false; refreshUI(); };
const openAdmin = () => { S.adminOpen = true; $("admin-email").value = CONFIG.adminEmail || ""; $("admin-error").textContent = ""; refreshUI(); };
$("btn-admin-open").onclick = openAdmin;
$("btn-admin-open2").onclick = openAdmin;
$("btn-admin-close").onclick = () => { S.adminOpen = false; refreshUI(); };
$("admin-form").onsubmit = async e => {
  e.preventDefault();
  $("admin-error").textContent = "";
  try {
    await signInWithEmailAndPassword(auth, $("admin-email").value.trim(), $("admin-pw").value);
    $("admin-pw").value = "";
    S.adminOpen = false; refreshUI();
  } catch (err) {
    $("admin-error").textContent = "로그인 실패: 이메일 또는 비밀번호를 확인하세요. (" + (err.code || "오류") + ")";
  }
};
$("btn-logout").onclick = () => signOut(auth);
$("btn-retry").onclick = () => {
  if (S.kicked) { S.kicked = false; S.fatal = null; claimPresence(); maybeSpawn(); refreshUI(); }
  else location.reload();
};
$("btn-start").onclick = e => adminCmd("start", e.currentTarget);
$("btn-clean").onclick = e => adminCmd("clean", e.currentTarget);
$("btn-reset").onclick = e => adminCmd("reset", e.currentTarget);
$("ap-end").onclick = e => adminCmd("end", e.currentTarget);
$("ap-restart").onclick = e => adminCmd("restart", e.currentTarget);
$("ap-reset").onclick = e => adminCmd("reset", e.currentTarget);
$("btn-over-close").onclick = () => { if (S.result) S.overSeen = S.result.gameId; refreshUI(); };
$("board-toggle").onclick = () => $("board").classList.toggle("collapsed");
if (innerWidth < 760) $("board").classList.add("collapsed");
$("duration").value = GC.initialGameDurationSeconds || 300;

// ───────────────────────── 입력 ─────────────────────────
const canvas = $("game"), ctx = canvas.getContext("2d");
const I = { mode: "mouse", mouse: null, mouseBoost: false, keys: new Set(), keyBoost: false, joy: null, boostTouch: null, btnBoost: false, angle: 0 };

canvas.addEventListener("pointerdown", e => {
  if (e.pointerType === "mouse") { if (e.button === 0) I.mouseBoost = true; return; }
  e.preventDefault();
  if (!I.joy) { I.joy = { id: e.pointerId, ox: e.clientX, oy: e.clientY, x: e.clientX, y: e.clientY }; I.mode = "touch"; }
  else if (I.boostTouch == null) I.boostTouch = e.pointerId; // 두 번째 손가락: 부스트
  canvas.setPointerCapture(e.pointerId);
});
canvas.addEventListener("pointermove", e => {
  if (e.pointerType === "mouse") {
    if (I.mouse && I.mode !== "mouse" && Math.hypot(e.clientX - I.mouse.x, e.clientY - I.mouse.y) < 6) return;
    I.mouse = { x: e.clientX, y: e.clientY }; I.mode = "mouse"; return;
  }
  if (I.joy && e.pointerId === I.joy.id) {
    I.joy.x = e.clientX; I.joy.y = e.clientY;
    const dx = I.joy.x - I.joy.ox, dy = I.joy.y - I.joy.oy;
    if (Math.hypot(dx, dy) > 8) I.angle = Math.atan2(dy, dx);
  }
});
const endPointer = e => {
  if (e.pointerType === "mouse") { I.mouseBoost = false; return; }
  if (I.joy && e.pointerId === I.joy.id) I.joy = null;
  if (e.pointerId === I.boostTouch) I.boostTouch = null;
};
canvas.addEventListener("pointerup", endPointer);
canvas.addEventListener("pointercancel", endPointer);
canvas.addEventListener("contextmenu", e => e.preventDefault());
addEventListener("mouseup", () => { I.mouseBoost = false; });

const KEYMAP = { ArrowUp: [0, -1], KeyW: [0, -1], ArrowDown: [0, 1], KeyS: [0, 1], ArrowLeft: [-1, 0], KeyA: [-1, 0], ArrowRight: [1, 0], KeyD: [1, 0] };
function keyAngle() {
  let x = 0, y = 0;
  for (const k of I.keys) { x += KEYMAP[k][0]; y += KEYMAP[k][1]; }
  if (x || y) { I.angle = Math.atan2(y, x); I.mode = "keys"; }
}
addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT") return;
  if (KEYMAP[e.code]) { I.keys.add(e.code); keyAngle(); e.preventDefault(); }
  if (e.code === "Space") { I.keyBoost = true; e.preventDefault(); }
});
addEventListener("keyup", e => {
  if (KEYMAP[e.code]) { I.keys.delete(e.code); keyAngle(); }
  if (e.code === "Space") I.keyBoost = false;
});
addEventListener("blur", () => { I.keys.clear(); I.keyBoost = I.mouseBoost = I.btnBoost = false; });

const boostBtn = $("boost");
boostBtn.addEventListener("pointerdown", e => { e.preventDefault(); e.stopPropagation(); I.btnBoost = true; boostBtn.classList.add("on"); boostBtn.setPointerCapture(e.pointerId); });
const boostOff = () => { I.btnBoost = false; boostBtn.classList.remove("on"); };
boostBtn.addEventListener("pointerup", boostOff);
boostBtn.addEventListener("pointercancel", boostOff);
document.addEventListener("gesturestart", e => e.preventDefault());
document.addEventListener("dblclick", e => e.preventDefault());

// 백그라운드: 내 뱀은 제자리에 멈춘 장애물이 됨. 돌아오면 1.5초 보호 후 다시 움직임.
document.addEventListener("visibilitychange", () => {
  if (document.hidden) {
    I.keys.clear(); I.keyBoost = I.mouseBoost = I.btnBoost = false; I.joy = null; I.boostTouch = null; boostOff();
    if (S.me) { S.me.paused = true; S.me.boost = false; writeHead(); writeBody(); }
  } else {
    if (S.me) {
      S.me.paused = false; S.me.invulnUntil = serverNow() + RETURN_SHIELD_MS; writeHead();
      if (S.connected) setConn("ok", "연결됨");
    }
    lastFrame = performance.now();
    maybeSpawn();
  }
});
addEventListener("pagehide", () => { if (S.me) { S.me.paused = true; writeHead(); writeBody(); } });

// ───────────────────────── 렌더링 ─────────────────────────
let W = 0, H = 0, DPR = 1, lastFrame = performance.now(), lastMini = 0;
function resize() {
  DPR = Math.min(2, devicePixelRatio || 1);
  W = innerWidth; H = innerHeight;
  canvas.width = W * DPR; canvas.height = H * DPR;
}
addEventListener("resize", resize);
resize();
const mini = $("minimap"), mctx = mini.getContext("2d");

function otherHead(h, now) {
  const a = Math.min(1, Math.max(0, (now - h.t) / SYNC_MS));
  const p0 = h.pts[0], p1 = h.pts[1] || p0;
  const seg = Math.hypot(p0[0] - p1[0], p0[1] - p1[1]);
  return { x: p1[0] + (p0[0] - p1[0]) * a, y: p1[1] + (p0[1] - p1[1]) * a, back: seg * (1 - a) };
}

function drawSnake(pts, hx, hy, len, hue, dashOff, boost, name, isMe, alpha, label) {
  if (!pts.length) return;
  const r = radius(len);
  ctx.globalAlpha = alpha;
  ctx.beginPath();
  ctx.moveTo(hx, hy);
  for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i][0], pts[i][1]);
  ctx.lineCap = ctx.lineJoin = "round";
  if (boost) { ctx.strokeStyle = `hsla(${hue},100%,65%,0.25)`; ctx.lineWidth = r * 2 + 14; ctx.stroke(); }
  ctx.strokeStyle = `hsl(${hue},65%,24%)`; ctx.lineWidth = r * 2 + 4; ctx.stroke();
  ctx.strokeStyle = `hsl(${hue},78%,52%)`; ctx.lineWidth = r * 2; ctx.stroke();
  ctx.setLineDash([r * 0.9, r * 1.3]);
  ctx.lineDashOffset = dashOff;
  ctx.strokeStyle = `hsla(${hue},95%,75%,0.45)`; ctx.lineWidth = r * 1.2; ctx.stroke();
  ctx.setLineDash([]);
  const p = pts[1] || pts[0];
  const ang = Math.atan2(hy - p[1], hx - p[0]) || 0;
  ctx.fillStyle = `hsl(${hue},85%,60%)`;
  ctx.beginPath(); ctx.arc(hx, hy, r * 1.1, 0, Math.PI * 2); ctx.fill();
  ctx.lineWidth = 2; ctx.strokeStyle = `hsl(${hue},65%,24%)`; ctx.stroke();
  const ex = Math.cos(ang), ey = Math.sin(ang), px = -ey, py = ex;
  for (const s of [-1, 1]) {
    const cx = hx + ex * r * 0.35 + px * s * r * 0.48, cy = hy + ey * r * 0.35 + py * s * r * 0.48;
    ctx.fillStyle = "#fff"; ctx.beginPath(); ctx.arc(cx, cy, r * 0.34, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = "#0b1020"; ctx.beginPath(); ctx.arc(cx + ex * r * 0.13, cy + ey * r * 0.13, r * 0.18, 0, Math.PI * 2); ctx.fill();
  }
  ctx.globalAlpha = 1;
  const z = S.cam.z, text = label ? `${name} · ${label}` : name;
  ctx.font = `${isMe ? 700 : 600} ${13 / z}px Pretendard, sans-serif`;
  ctx.textAlign = "center";
  ctx.lineWidth = 3 / z; ctx.strokeStyle = "rgba(0,0,0,.6)";
  ctx.strokeText(text, hx, hy - r - 10 / z);
  ctx.fillStyle = isMe ? "#3ee6a8" : label ? "#ffd166" : "rgba(230,237,247,.9)";
  ctx.fillText(text, hx, hy - r - 10 / z);
}

function frame(now) {
  requestAnimationFrame(frame);
  const dt = Math.min(0.1, (now - lastFrame) / 1000);
  lastFrame = now;
  const st = gameStatus();
  if (st !== S.lastStatus) { const prev = S.lastStatus; S.lastStatus = st; onStatus(st, prev); }
  if (S.me && st === "running" && !document.hidden && !S.me.paused) simulate(dt);

  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const me = S.me;
  let target = null, len = INIT_LEN;
  if (me) { target = me.pts[0]; len = me.len; }
  else {
    const leader = S.lb.find(r => r.alive && S.heads.get(r.uid) && S.heads.get(r.uid).pts.length);
    if (leader) { const h = S.heads.get(leader.uid); const hd = otherHead(h, now); target = [hd.x, hd.y]; }
  }
  const base = Math.min(W, H) / (isTouch ? 760 : 980);
  const zt = target ? base * Math.pow(1 + Math.max(0, len - 5) / 120, -0.35) : Math.min(W, H) / (ARENA_R * 2.3);
  const cam = S.cam;
  if (!target) target = [Math.cos(now / 9000) * 300, Math.sin(now / 9000) * 300];
  const k = me ? 0.25 : 0.06;
  cam.x += (target[0] - cam.x) * k; cam.y += (target[1] - cam.y) * k; cam.z += (zt - cam.z) * 0.05;
  const z = cam.z;

  ctx.fillStyle = "#120a12"; ctx.fillRect(0, 0, W, H);
  ctx.save();
  ctx.translate(W / 2, H / 2); ctx.scale(z, z); ctx.translate(-cam.x, -cam.y);
  const vx0 = cam.x - W / 2 / z, vx1 = cam.x + W / 2 / z, vy0 = cam.y - H / 2 / z, vy1 = cam.y + H / 2 / z;

  // 경기장 + 그리드
  ctx.beginPath(); ctx.arc(0, 0, ARENA_R, 0, Math.PI * 2);
  ctx.fillStyle = "#0b1222"; ctx.fill();
  ctx.save(); ctx.clip();
  const g = 64;
  ctx.strokeStyle = "rgba(120,150,210,0.07)"; ctx.lineWidth = 1 / z;
  ctx.beginPath();
  for (let x = Math.floor(vx0 / g) * g; x <= vx1; x += g) { ctx.moveTo(x, vy0); ctx.lineTo(x, vy1); }
  for (let y = Math.floor(vy0 / g) * g; y <= vy1; y += g) { ctx.moveTo(vx0, y); ctx.lineTo(vx1, y); }
  ctx.stroke();
  ctx.restore();
  ctx.beginPath(); ctx.arc(0, 0, ARENA_R, 0, Math.PI * 2);
  ctx.strokeStyle = "rgba(255,92,122,0.18)"; ctx.lineWidth = 26; ctx.stroke();
  ctx.strokeStyle = "rgba(255,92,122,0.75)"; ctx.lineWidth = 4; ctx.stroke();

  // 먹이
  if (st !== "waiting") {
    const t = now / 1000;
    const drawFood = (x, y, v, h, seed) => {
      if (x < vx0 - 20 || x > vx1 + 20 || y < vy0 - 20 || y > vy1 + 20) return;
      const r = (3.5 + v * 1.4) * (1 + 0.12 * Math.sin(t * 3 + seed));
      ctx.fillStyle = `hsla(${h},95%,60%,0.18)`;
      ctx.beginPath(); ctx.arc(x, y, r * 2.3, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = `hsl(${h},95%,66%)`;
      ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill();
    };
    for (const f of S.natural) if (!S.pending.has("n" + f.i)) drawFood(f.x, f.y, f.v, f.h, f.i);
    let n = 0;
    for (const [key, f] of S.drops) if (!S.pending.has("d" + key)) drawFood(f.x, f.y, f.v, f.h, n++);
  }

  // 다른 뱀
  for (const [u, h] of S.heads) {
    if (u === myUid() || !h.data || h.data.d || !S.meta || h.data.g !== S.meta.gameId || !h.pts.length) continue;
    const hd = otherHead(h, now);
    const p = S.players[u];
    const label = h.data.p ? "자리 비움" : p && p.online === false ? "연결 끊김" : "";
    drawSnake(h.pts, hd.x, hd.y, h.data.l, hueOf(u), -(h.odo - hd.back), !!h.data.b, h.data.n || "", false, label ? 0.75 : 1, label);
  }
  // 내 뱀 (맨 위)
  S.myHead = null;
  if (me) {
    const shield = serverNow() < me.invulnUntil;
    const alpha = shield ? 0.45 + 0.25 * Math.sin(now / 80) : 1;
    drawSnake(me.pts, me.pts[0][0], me.pts[0][1], me.len, hueOf(myUid()), -me.odo, me.boost && st === "running",
      (myPlayer() && myPlayer().name) || "", true, alpha, "");
    S.myHead = [(me.pts[0][0] - cam.x) * z + W / 2, (me.pts[0][1] - cam.y) * z + H / 2];
  }

  // 탈락 효과
  S.fx = S.fx.filter(fx => now - fx.t < 700);
  for (const fx of S.fx) {
    const p = (now - fx.t) / 700;
    ctx.strokeStyle = `hsla(${fx.h},100%,70%,${1 - p})`; ctx.lineWidth = 4 / z;
    ctx.beginPath(); ctx.arc(fx.x, fx.y, 20 + p * 90, 0, Math.PI * 2); ctx.stroke();
  }
  ctx.restore();

  // 가상 조이스틱
  if (I.joy) {
    ctx.strokeStyle = "rgba(255,255,255,.25)"; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.arc(I.joy.ox, I.joy.oy, 46, 0, Math.PI * 2); ctx.stroke();
    const dx = I.joy.x - I.joy.ox, dy = I.joy.y - I.joy.oy, d = Math.hypot(dx, dy), m = Math.min(d, 46) / (d || 1);
    ctx.fillStyle = "rgba(62,230,168,.45)";
    ctx.beginPath(); ctx.arc(I.joy.ox + dx * m, I.joy.oy + dy * m, 20, 0, Math.PI * 2); ctx.fill();
  }

  drawHud(st);
  if (now - lastMini > 120 && !mini.classList.contains("hidden")) { lastMini = now; drawMinimap(); }
}

let lastHudText = "";
function drawHud(st) {
  let txt = "--:--";
  if (st === "running") txt = fmtTime(S.meta.endsAt - serverNow());
  else if (st === "countdown") { txt = fmtTime(S.meta.endsAt - S.meta.startedAt); $("countdown").textContent = Math.ceil((S.meta.startedAt - serverNow()) / 1000); }
  else if (st === "finished") txt = "종료";
  if (txt !== lastHudText) {
    lastHudText = txt;
    $("time").textContent = txt;
    $("hud-time").classList.toggle("warn", st === "running" && S.meta.endsAt - serverNow() < 30000);
    if (S.isAdmin && S.meta) {
      const hs = inGameHeads();
      $("ap-status").textContent = `상태: ${{ running: "진행 중", countdown: "시작 대기", finished: "종료" }[st] || "-"}`;
      $("ap-count").textContent = `참가자: ${hs.length}명 (생존 ${hs.filter(([, h]) => !h.data.d).length})`;
      $("ap-time").textContent = `남은 시간: ${txt}`;
    }
  }
  if (S.me) { $("my-score").textContent = S.me.score; $("my-len").textContent = Math.floor(S.me.len); }
}

function drawMinimap() {
  const w = mini.clientWidth || 150, d = Math.min(2, devicePixelRatio || 1);
  if (mini.width !== w * d) { mini.width = w * d; mini.height = w * d; }
  mctx.setTransform(d, 0, 0, d, 0, 0);
  mctx.clearRect(0, 0, w, w);
  const s = (w / 2 - 6) / ARENA_R, c = w / 2;
  mctx.strokeStyle = "rgba(255,92,122,.5)"; mctx.lineWidth = 1.5;
  mctx.beginPath(); mctx.arc(c, c, ARENA_R * s, 0, Math.PI * 2); mctx.stroke();
  const z = S.cam.z;
  mctx.strokeStyle = "rgba(255,255,255,.18)"; mctx.lineWidth = 1;
  mctx.strokeRect(c + (S.cam.x - W / 2 / z) * s, c + (S.cam.y - H / 2 / z) * s, W / z * s, H / z * s);
  for (const [u, h] of S.heads) {
    if (u === myUid() || !h.data || h.data.d || !h.pts.length) continue;
    mctx.fillStyle = `hsl(${hueOf(u)},80%,60%)`;
    mctx.beginPath(); mctx.arc(c + h.pts[0][0] * s, c + h.pts[0][1] * s, 2 + Math.min(3, h.data.l / 80), 0, Math.PI * 2); mctx.fill();
  }
  if (S.me) {
    mctx.fillStyle = "#fff";
    mctx.beginPath(); mctx.arc(c + S.me.pts[0][0] * s, c + S.me.pts[0][1] * s, 3.5, 0, Math.PI * 2); mctx.fill();
  }
}

if (/[?&]debug\b/.test(location.search)) window.__snake = { S, I, leaderboard, gameStatus }; // 테스트용

requestAnimationFrame(frame);
refreshUI();
