// ────────────────────────────────────────────────────────────────
// 이 파일만 수정하면 됩니다. (공개되어도 되는 값만 넣으세요. 비밀번호는 절대 넣지 마세요)
// ────────────────────────────────────────────────────────────────
export const CONFIG = {
  // Firebase 콘솔 → 프로젝트 설정(톱니바퀴) → 일반 → 내 앱 → 웹 앱의 "SDK 설정 및 구성"에서 복사
  firebase: {
    apiKey: "YOUR_FIREBASE_API_KEY",
    authDomain: "YOUR_PROJECT_ID.firebaseapp.com",
    databaseURL: "https://YOUR_PROJECT_ID-default-rtdb.firebaseio.com",
    projectId: "YOUR_PROJECT_ID",
    storageBucket: "YOUR_PROJECT_ID.appspot.com",
    messagingSenderId: "YOUR_FIREBASE_MESSAGING_SENDER_ID",
    appId: "YOUR_FIREBASE_APP_ID"
  },

  // Firebase Authentication에 이메일/비밀번호 사용자로 등록한 관리자 이메일.
  // 관리자 로그인 창에 미리 채워지는 값일 뿐이며, 실제 권한은 DB의 admins/{UID} 등록 여부로 결정됩니다.
  adminEmail: "admin@snake-arena.game",

  game: {
    maxPlayers: 20,                 // 최대 20 (DB 규칙의 자리 번호 0~19와 연결)
    initialGameDurationSeconds: 300,// 관리자가 시작할 때 기본 게임 시간
    initialSnakeLength: 5,
    reconnectGraceSeconds: 60,      // 바꾸면 database.rules.json의 60000도 같이 바꾸세요
    syncRate: 8,                    // 초당 위치 전송 횟수(4~15). 낮출수록 무료 사용량 절약
    arenaRadius: 2200,
    foodCount: 350
  }
};
