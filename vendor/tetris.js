/* Falling-block well.
   idea after @ospann (ospann/tetris); clean-room implementation, no code copied. */
(function () {
  "use strict";

  var COLS = 10;
  var ROWS = 20;
  var FONT = "ui-sans-serif, system-ui, sans-serif";
  var INK = {
    I: "#3ec8d8",
    O: "#e2b14a",
    T: "#b06ad6",
    S: "#3cbe78",
    Z: "#e25b4a",
    J: "#4a78e2",
    L: "#e8883a"
  };
  var BASE = {
    I: [[0, 0], [1, 0], [2, 0], [3, 0]],
    O: [[0, 0], [1, 0], [0, 1], [1, 1]],
    T: [[0, 0], [1, 0], [2, 0], [1, 1]],
    S: [[1, 0], [2, 0], [0, 1], [1, 1]],
    Z: [[0, 0], [1, 0], [1, 1], [2, 1]],
    J: [[0, 0], [0, 1], [1, 1], [2, 1]],
    L: [[2, 0], [0, 1], [1, 1], [2, 1]]
  };
  var KICKS = [[0, 0], [-1, 0], [1, 0], [0, -1], [-2, 0], [2, 0], [0, -2], [-1, -1], [1, -1]];
  var OPEN = ["LL.SSZZ.II", "LLTSSZZOO.", "JJTT.ZOO.I", "JJJTT.OOII"];
  var LINE_SCORE = [0, 100, 300, 500, 800];

  function spin(cells) {
    var out = [];
    var i;
    var minx = 99;
    var miny = 99;
    for (i = 0; i < cells.length; i++) out.push([-cells[i][1], cells[i][0]]);
    for (i = 0; i < out.length; i++) {
      if (out[i][0] < minx) minx = out[i][0];
      if (out[i][1] < miny) miny = out[i][1];
    }
    for (i = 0; i < out.length; i++) {
      out[i][0] -= minx;
      out[i][1] -= miny;
    }
    return out;
  }

  var ROTS = {};
  var KINDS = ["I", "O", "T", "S", "Z", "J", "L"];
  var ki;
  for (ki = 0; ki < KINDS.length; ki++) {
    var cur = BASE[KINDS[ki]];
    ROTS[KINDS[ki]] = [cur];
    var s;
    for (s = 0; s < 3; s++) {
      cur = spin(cur);
      ROTS[KINDS[ki]].push(cur);
    }
  }

  var seed = 0x5a17c3;
  function rnd() {
    seed = (seed * 1664525 + 1013904223) >>> 0;
    return seed / 4294967296;
  }

  var board = [];
  var bag = [];
  var queue = [];
  var hold = null;
  var canHold = true;
  var piece = null;
  var over = false;
  var score = 0;
  var lines = 0;
  var dropAcc = 0;
  var lockMs = 0;
  var lockResets = 0;
  var softHeld = false;
  var grounded = false;
  var heldActs = { left: 0, right: 0 };
  var repeatAt = { left: 0, right: 0 };
  var sparks = [];
  var dust = [];
  var dustReady = false;
  var viewW = 390;
  var viewH = 844;
  var laidKey = "";
  var hot = { well: null, restart: null, card: null, cell: 16 };
  var gesture = null;
  var audio = null;
  var sent = false;
  var paintedOnce = false;
  var lastT = 0;

  function emptyRow() {
    var row = [];
    var x;
    for (x = 0; x < COLS; x++) row.push("");
    return row;
  }

  function levelOf(n) {
    return 1 + ((n / 10) | 0);
  }

  function dropInterval() {
    var lv = levelOf(lines);
    var ms = 820;
    var i;
    for (i = 1; i < lv; i++) ms *= 0.82;
    if (ms < 90) ms = 90;
    return ms;
  }

  function bounds(type, rot) {
    var cells = ROTS[type][rot];
    var minx = 99;
    var miny = 99;
    var maxx = -99;
    var maxy = -99;
    var i;
    for (i = 0; i < cells.length; i++) {
      var c = cells[i];
      if (c[0] < minx) minx = c[0];
      if (c[1] < miny) miny = c[1];
      if (c[0] > maxx) maxx = c[0];
      if (c[1] > maxy) maxy = c[1];
    }
    return { minx: minx, miny: miny, maxx: maxx, maxy: maxy };
  }

  function fits(type, rot, px, py) {
    var cells = ROTS[type][rot];
    var i;
    for (i = 0; i < cells.length; i++) {
      var x = px + cells[i][0];
      var y = py + cells[i][1];
      if (x < 0 || x >= COLS || y >= ROWS) return false;
      if (y >= 0 && board[y][x]) return false;
    }
    return true;
  }

  function placeSpawn(p) {
    var b = bounds(p.type, p.rot);
    p.x = (((COLS - (b.maxx - b.minx + 1)) / 2) | 0) - b.minx;
    p.y = -b.miny;
  }

  function pullBag() {
    if (!bag.length) {
      bag = KINDS.slice();
      var i;
      for (i = bag.length - 1; i > 0; i--) {
        var j = Math.floor(Math.random() * (i + 1));
        var t = bag[i];
        bag[i] = bag[j];
        bag[j] = t;
      }
    }
    return bag.pop();
  }

  function ensureQueue() {
    while (queue.length < 5) queue.push(pullBag());
  }

  function stampOpen() {
    var i;
    for (i = 0; i < OPEN.length; i++) {
      var y = ROWS - OPEN.length + i;
      var x;
      for (x = 0; x < COLS; x++) {
        var ch = OPEN[i].charAt(x);
        board[y][x] = ch === "." ? "" : ch;
      }
    }
  }

  function spawn() {
    ensureQueue();
    var type = queue.shift();
    ensureQueue();
    piece = { type: type, rot: 0, x: 0, y: 0 };
    placeSpawn(piece);
    lockMs = 0;
    lockResets = 0;
    canHold = true;
    dropAcc = 0;
    if (!fits(piece.type, piece.rot, piece.x, piece.y)) {
      piece.y -= 1;
      if (!fits(piece.type, piece.rot, piece.x, piece.y)) over = true;
    }
  }

  function bootGame(opening) {
    var y;
    board = [];
    for (y = 0; y < ROWS; y++) board.push(emptyRow());
    bag = [];
    queue = [];
    hold = null;
    canHold = true;
    piece = null;
    over = false;
    score = 0;
    lines = 0;
    dropAcc = 0;
    lockMs = 0;
    lockResets = 0;
    softHeld = false;
    grounded = false;
    sparks = [];
    if (opening) {
      stampOpen();
      queue = ["T", "I", "O", "L", "S", "Z", "J"];
    }
    spawn();
    if (opening && piece && fits(piece.type, piece.rot, piece.x, 2)) piece.y = 2;
  }

  function nudgeLock() {
    if (lockResets < 14) {
      lockMs = 0;
      lockResets += 1;
    }
  }

  function shift(dx) {
    if (over || !piece) return false;
    if (!fits(piece.type, piece.rot, piece.x + dx, piece.y)) return false;
    piece.x += dx;
    nudgeLock();
    return true;
  }

  function turn() {
    if (over || !piece) return false;
    var nr = (piece.rot + 1) % 4;
    var i;
    for (i = 0; i < KICKS.length; i++) {
      var ox = KICKS[i][0];
      var oy = KICKS[i][1];
      if (fits(piece.type, nr, piece.x + ox, piece.y + oy)) {
        piece.rot = nr;
        piece.x += ox;
        piece.y += oy;
        nudgeLock();
        blip(360, 0.05, "triangle", 0.04);
        return true;
      }
    }
    return false;
  }

  function clearLines() {
    var cleared = 0;
    var y = ROWS - 1;
    while (y >= 0) {
      var full = true;
      var x;
      for (x = 0; x < COLS; x++) {
        if (!board[y][x]) {
          full = false;
          break;
        }
      }
      if (full) {
        board.splice(y, 1);
        board.unshift(emptyRow());
        cleared += 1;
      } else {
        y -= 1;
      }
    }
    return cleared;
  }

  function burstAt(row) {
    var i;
    for (i = 0; i < 8; i++) {
      sparks.push({
        c: rnd() * COLS,
        r: row + rnd(),
        vx: (rnd() - 0.5) * 8,
        vy: -1.5 - rnd() * 3,
        life: 0.28 + rnd() * 0.22,
        color: INK[KINDS[(rnd() * KINDS.length) | 0]]
      });
    }
    if (sparks.length > 64) sparks.splice(0, sparks.length - 64);
  }

  function commit() {
    if (!piece || over) return;
    var cells = ROTS[piece.type][piece.rot];
    var color = piece.type;
    var i;
    var topRow = ROWS;
    for (i = 0; i < cells.length; i++) {
      var x = piece.x + cells[i][0];
      var y = piece.y + cells[i][1];
      if (y < topRow) topRow = y;
      if (y >= 0 && y < ROWS && x >= 0 && x < COLS) board[y][x] = color;
    }
    var n = clearLines();
    if (n) {
      var lv = levelOf(lines);
      score += LINE_SCORE[n] * lv;
      lines += n;
      burstAt(topRow < 0 ? 0 : topRow);
      blip(420, 0.08, "triangle", 0.05);
      if (n > 1) blip(420 + n * 80, 0.16, "triangle", 0.05);
    } else {
      blip(140, 0.05, "square", 0.03);
    }
    piece = null;
    spawn();
    if (over) blip(90, 0.22, "sawtooth", 0.04);
  }

  function softStep() {
    if (over || !piece) return;
    if (!fits(piece.type, piece.rot, piece.x, piece.y + 1)) return;
    piece.y += 1;
    score += 1;
    lockMs = 0;
    dropAcc = 0;
  }

  function hardDrop() {
    if (over || !piece) return;
    var n = 0;
    while (fits(piece.type, piece.rot, piece.x, piece.y + 1)) {
      piece.y += 1;
      n += 1;
    }
    score += n * 2;
    blip(110, 0.07, "square", 0.05);
    commit();
  }

  function doHold() {
    if (over || !piece || !canHold) return;
    var incoming = hold;
    hold = piece.type;
    canHold = false;
    if (incoming) {
      piece = { type: incoming, rot: 0, x: 0, y: 0 };
      placeSpawn(piece);
      lockMs = 0;
      lockResets = 0;
      dropAcc = 0;
      if (!fits(piece.type, piece.rot, piece.x, piece.y)) over = true;
    } else {
      spawn();
      canHold = false;
    }
    blip(280, 0.07, "square", 0.04);
  }

  function pressAct(act) {
    if (act === "left") {
      if (shift(-1)) blip(210, 0.03, "square", 0.018);
    } else if (act === "right") {
      if (shift(1)) blip(210, 0.03, "square", 0.018);
    } else if (act === "rot") turn();
    else if (act === "soft") softStep();
    else if (act === "hard") hardDrop();
    else if (act === "hold") doHold();
  }

  function tickHeld() {
    var now = performance.now();
    var names = ["left", "right"];
    var i;
    for (i = 0; i < names.length; i++) {
      var n = names[i];
      if (heldActs[n] > 0 && now >= repeatAt[n]) {
        pressAct(n);
        repeatAt[n] = now + 48;
      }
    }
  }

  function update(dt) {
    tickMotes(dt);
    tickHeld();
    if (over || !piece) return;
    var iv = softHeld ? 46 : dropInterval();
    if (fits(piece.type, piece.rot, piece.x, piece.y + 1)) {
      if (grounded) dropAcc = iv;
      grounded = false;
      lockMs = 0;
      dropAcc += dt;
      if (dropAcc >= iv) {
        dropAcc -= iv;
        if (dropAcc > iv) dropAcc = 0;
        piece.y += 1;
        if (softHeld) score += 1;
      }
    } else {
      grounded = true;
      dropAcc = 0;
      if (softHeld) {
        commit();
      } else {
        lockMs += dt;
        if (lockMs >= 450) commit();
      }
    }
  }

  function tickMotes(dt) {
    var sec = dt / 1000;
    var i;
    for (i = sparks.length - 1; i >= 0; i--) {
      var p = sparks[i];
      p.c += p.vx * sec;
      p.r += p.vy * sec;
      p.vy += 7 * sec;
      p.life -= sec;
      if (p.life <= 0) sparks.splice(i, 1);
    }
    for (i = 0; i < dust.length; i++) {
      var d = dust[i];
      d.y -= d.v * sec;
      if (d.y < -8) d.y = viewH + 8;
    }
  }

  function arm() {
    if (audio) {
      if (audio.state === "suspended" && audio.resume) audio.resume();
      return;
    }
    var AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    try {
      audio = new AC();
      if (audio.resume) audio.resume();
    } catch (err) {
      audio = null;
    }
  }

  function blip(freq, dur, type, gain) {
    if (!audio) return;
    var t = audio.currentTime;
    var o = audio.createOscillator();
    var g = audio.createGain();
    o.type = type || "square";
    o.frequency.setValueAtTime(freq, t);
    g.gain.setValueAtTime(gain || 0.04, t);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    o.connect(g);
    g.connect(audio.destination);
    o.start(t);
    o.stop(t + dur + 0.02);
  }

  function metrics(w, h) {
    var edge = 8;
    var gear = 54;
    var gap = 6;
    var btn = h >= 700 ? 56 : 48;
    var limit = w - edge * 2;
    var row = btn * 6 + gap * 5;
    if (row > limit) {
      gap = 4;
      btn = Math.floor((limit - gap * 5) / 6);
      if (btn < 44) btn = 44;
    }
    var padTop = h - edge - btn;
    var creditH = 26;
    var creditTop = padTop - 6 - creditH;
    var tall = h >= 640;
    var hudH = tall ? 58 : 48;
    var hudTop = 8;
    var fieldTop = hudTop + hudH + 6;
    var fieldBot = creditTop - 6;
    var fieldH = fieldBot - fieldTop;
    var fieldW = w - edge * 2;
    var frame = 6;
    var side = 0;
    var sideGap = 8;
    if (!tall && fieldH > 40) {
      var cellTry = Math.floor((fieldH - frame * 2) / ROWS);
      if (cellTry < 8) cellTry = 8;
      var wellTry = cellTry * COLS;
      var need = 64 * 2 + sideGap * 2;
      if (fieldW - wellTry >= need) {
        side = Math.floor((fieldW - wellTry) / 2) - sideGap;
        if (side > 96) side = 96;
        if (side < 64) side = 0;
      }
    }
    var innerW = fieldW - (side ? side * 2 + sideGap * 2 : 0) - frame * 2;
    var innerH = fieldH - frame * 2;
    var cell = Math.floor(Math.min(innerW / COLS, innerH / ROWS));
    if (cell < 8) cell = 8;
    var wellW = cell * COLS;
    var wellH = cell * ROWS;
    var groupW = wellW + frame * 2 + (side ? side * 2 + sideGap * 2 : 0);
    var guard = 0;
    while (guard < 16 && cell > 8 && (groupW > fieldW || wellH + frame * 2 > fieldH)) {
      cell -= 1;
      wellW = cell * COLS;
      wellH = cell * ROWS;
      groupW = wellW + frame * 2 + (side ? side * 2 + sideGap * 2 : 0);
      guard += 1;
    }
    var gx = edge + Math.floor((fieldW - groupW) / 2);
    var gy = fieldTop + Math.floor((fieldH - (wellH + frame * 2)) / 2);
    var well = {
      x: gx + frame + (side ? side + sideGap : 0),
      y: gy + frame,
      w: wellW,
      h: wellH,
      cell: cell
    };
    var holdBox = null;
    var nextBox = null;
    if (side) {
      holdBox = { x: gx, y: well.y, w: side, h: Math.min(side + 36, Math.floor(wellH * 0.46)) };
      nextBox = {
        x: well.x + wellW + frame + sideGap,
        y: well.y,
        w: side,
        h: Math.min(wellH, side * 3 + 28)
      };
      if (nextBox.x + nextBox.w > w - 4) nextBox.w = w - 4 - nextBox.x;
      if (nextBox.w < 56) nextBox = null;
      if (holdBox.x < 4) holdBox.x = 4;
    }
    if (well.y + well.h > creditTop - 4) {
      var lift = well.y + well.h - (creditTop - 4);
      if (well.y - lift >= fieldTop) well.y -= lift;
    }
    return {
      w: w,
      h: h,
      btn: btn,
      gap: gap,
      padTop: padTop,
      tall: tall,
      creditTop: creditTop,
      creditH: creditH,
      hud: { x: edge, y: hudTop, w: w - edge - gear, h: hudH },
      well: well,
      frame: frame,
      hold: holdBox,
      next: nextBox,
      restart: {
        x: edge,
        y: hudTop + Math.floor((hudH - 44) / 2),
        w: 44,
        h: 44
      }
    };
  }

  function roundRect(ctx, x, y, w, h, r) {
    var rad = r;
    if (rad > w / 2) rad = w / 2;
    if (rad > h / 2) rad = h / 2;
    ctx.beginPath();
    ctx.moveTo(x + rad, y);
    ctx.arcTo(x + w, y, x + w, y + h, rad);
    ctx.arcTo(x + w, y + h, x, y + h, rad);
    ctx.arcTo(x, y + h, x, y, rad);
    ctx.arcTo(x, y, x + w, y, rad);
    ctx.closePath();
  }

  function tile(ctx, x, y, s, color, ghost) {
    var inset = s * 0.08;
    if (inset < 1) inset = 1;
    var rx = x + inset;
    var ry = y + inset;
    var rw = s - inset * 2;
    var rh = s - inset * 2;
    if (rw < 1 || rh < 1) return;
    var rad = s * 0.16;
    if (rad < 2) rad = 2;
    roundRect(ctx, rx, ry, rw, rh, rad);
    if (ghost) {
      ctx.strokeStyle = color;
      ctx.globalAlpha = 0.55;
      ctx.lineWidth = s * 0.07;
      if (ctx.lineWidth < 1) ctx.lineWidth = 1;
      ctx.stroke();
      ctx.globalAlpha = 1;
      return;
    }
    ctx.fillStyle = color;
    ctx.fill();
    ctx.strokeStyle = "rgba(0,0,0,0.35)";
    ctx.lineWidth = 1;
    ctx.stroke();
    ctx.fillStyle = "rgba(255,255,255,0.30)";
    ctx.fillRect(rx + 1, ry + 1, rw - 2, rh * 0.34);
    ctx.fillStyle = "rgba(0,0,0,0.16)";
    ctx.fillRect(rx + 1, ry + rh * 0.72, rw - 2, rh * 0.2);
  }

  function drawCellsIn(ctx, type, rot, x, y, w, h) {
    if (!type || w < 4 || h < 4) return;
    var cells = ROTS[type][rot];
    var b = bounds(type, rot);
    var cw = b.maxx - b.minx + 1;
    var ch = b.maxy - b.miny + 1;
    var s = Math.min(w / cw, h / ch);
    var ox = x + (w - s * cw) / 2 - b.minx * s;
    var oy = y + (h - s * ch) / 2 - b.miny * s;
    var i;
    for (i = 0; i < cells.length; i++) {
      tile(ctx, ox + cells[i][0] * s, oy + cells[i][1] * s, s, INK[type], false);
    }
  }

  function frameBox(ctx, box) {
    roundRect(ctx, box.x, box.y, box.w, box.h, 8);
    ctx.fillStyle = "rgba(8,10,18,0.78)";
    ctx.fill();
    ctx.strokeStyle = "rgba(232,206,160,0.38)";
    ctx.lineWidth = 1;
    ctx.stroke();
  }

  function drawHold(ctx, box) {
    if (!box) return;
    frameBox(ctx, box);
    ctx.fillStyle = "rgba(232,206,160,0.8)";
    ctx.font = "600 9px " + FONT;
    ctx.textAlign = "left";
    ctx.textBaseline = "top";
    ctx.fillText("HOLD", box.x + 6, box.y + 4);
    if (!hold) return;
    ctx.globalAlpha = canHold ? 1 : 0.45;
    drawCellsIn(ctx, hold, 0, box.x + 4, box.y + 16, box.w - 8, box.h - 20);
    ctx.globalAlpha = 1;
  }

  function drawNext(ctx, box) {
    if (!box) return;
    frameBox(ctx, box);
    ctx.fillStyle = "rgba(232,206,160,0.8)";
    ctx.font = "600 9px " + FONT;
    ctx.textAlign = "left";
    ctx.textBaseline = "top";
    ctx.fillText("NEXT", box.x + 6, box.y + 4);
    var n = 3;
    if (queue.length < n) n = queue.length;
    var top = box.y + 16;
    var slotH = (box.h - 20) / (n || 1);
    var i;
    for (i = 0; i < n; i++) {
      drawCellsIn(ctx, queue[i], 0, box.x + 4, top + i * slotH, box.w - 8, slotH - 2);
    }
  }

  function drawRestart(ctx, r) {
    var cx = r.x + r.w / 2;
    var cy = r.y + r.h / 2;
    ctx.beginPath();
    ctx.arc(cx, cy, 16, 0, Math.PI * 2);
    ctx.fillStyle = "rgba(18,22,38,0.92)";
    ctx.fill();
    ctx.strokeStyle = "rgba(232,206,160,0.75)";
    ctx.lineWidth = 1.5;
    ctx.stroke();
    ctx.beginPath();
    ctx.arc(cx, cy, 7, 0.5, Math.PI * 1.65);
    ctx.strokeStyle = "#f6edd8";
    ctx.lineWidth = 1.7;
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(cx + 5.2, cy - 7.2);
    ctx.lineTo(cx + 11, cy - 3.2);
    ctx.lineTo(cx + 4.2, cy - 1.4);
    ctx.closePath();
    ctx.fillStyle = "#f6edd8";
    ctx.fill();
  }

  function groupNum(n) {
    var s = String(n | 0);
    var out = "";
    while (s.length > 3) {
      out = "," + s.slice(-3) + out;
      s = s.slice(0, -3);
    }
    return s + out;
  }

  function drawHud(ctx, m) {
    drawRestart(ctx, m.restart);
    ctx.textBaseline = "middle";
    ctx.textAlign = "left";
    ctx.font = "700 15px " + FONT;
    var label = groupNum(score) + "   " + lines + " ln   Lv " + levelOf(lines);
    var tx = m.restart.x + m.restart.w + 8;
    var ty = m.hud.y + m.hud.h / 2;
    ctx.fillStyle = "#f6edd8";
    ctx.fillText(label, tx, ty);
    if (!m.tall) return;
    var tw = ctx.measureText(label).width;
    var x = tx + tw + 12;
    var right = m.hud.x + m.hud.w;
    var y = m.hud.y + 6;
    var boxH = m.hud.h - 12;
    if (right - x < 70 || boxH < 20) return;
    var holdW = 40;
    roundRect(ctx, x, y, holdW, boxH, 6);
    ctx.fillStyle = "rgba(8,10,18,0.72)";
    ctx.fill();
    if (hold) {
      ctx.globalAlpha = canHold ? 1 : 0.45;
      drawCellsIn(ctx, hold, 0, x + 2, y + 2, holdW - 4, boxH - 4);
      ctx.globalAlpha = 1;
    } else {
      ctx.fillStyle = "rgba(232,206,160,0.7)";
      ctx.font = "700 12px " + FONT;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText("H", x + holdW / 2, y + boxH / 2);
    }
    x += holdW + 6;
    var left = right - x;
    if (left < 36) return;
    var slots = left >= 112 ? 3 : 1;
    var slotW = Math.min(40, (left - (slots - 1) * 4) / slots);
    var i;
    for (i = 0; i < slots; i++) {
      if (!queue[i]) break;
      drawCellsIn(ctx, queue[i], 0, x, y, slotW, boxH);
      x += slotW + 4;
    }
  }

  function drawCredit(ctx, m) {
    var a = "idea after @ospann (ospann/tetris);";
    var b = "clean-room implementation, no code copied";
    var size = 11;
    ctx.font = size + "px " + FONT;
    var tw = ctx.measureText(a).width;
    var tw2 = ctx.measureText(b).width;
    if (tw2 > tw) tw = tw2;
    var room = m.w - 12;
    if (tw > room && tw > 0) size = size * (room / tw);
    if (size < 7) size = 7;
    ctx.font = size + "px " + FONT;
    ctx.fillStyle = "rgba(246,237,216,0.66)";
    ctx.textAlign = "center";
    ctx.textBaseline = "top";
    ctx.fillText(a, m.w / 2, m.creditTop);
    ctx.fillText(b, m.w / 2, m.creditTop + size + 2);
  }

  function ensureDust(w, h) {
    if (dustReady) return;
    dustReady = true;
    var i;
    for (i = 0; i < 16; i++) {
      dust.push({
        x: rnd() * w,
        y: rnd() * h,
        r: 0.6 + rnd() * 1.5,
        v: 6 + rnd() * 14,
        a: 0.12 + rnd() * 0.28
      });
    }
  }

  function drawScene(ctx, m) {
    var w = m.w;
    var h = m.h;
    var g = ctx.createLinearGradient(0, 0, 0, h);
    g.addColorStop(0, "#161a32");
    g.addColorStop(1, "#070814");
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, w, h);

    var i;
    for (i = 0; i < dust.length; i++) {
      var d = dust[i];
      ctx.beginPath();
      ctx.arc(d.x, d.y, d.r, 0, Math.PI * 2);
      ctx.fillStyle = "rgba(244,231,200," + d.a + ")";
      ctx.fill();
    }

    var well = m.well;
    var frame = m.frame;
    var fx = well.x - frame;
    var fy = well.y - frame;
    var fw = well.w + frame * 2;
    var fh = well.h + frame * 2;
    ctx.fillStyle = "rgba(0,0,0,0.35)";
    roundRect(ctx, fx + 3, fy + 7, fw, fh, 12);
    ctx.fill();
    roundRect(ctx, fx, fy, fw, fh, 10);
    ctx.fillStyle = "#0b0e18";
    ctx.fill();

    ctx.save();
    ctx.beginPath();
    ctx.rect(well.x, well.y, well.w, well.h);
    ctx.clip();
    ctx.strokeStyle = "rgba(232,206,160,0.10)";
    ctx.lineWidth = 1;
    var cell = well.cell;
    var x;
    var y;
    for (x = 0; x <= COLS; x++) {
      ctx.beginPath();
      ctx.moveTo(well.x + x * cell + 0.5, well.y);
      ctx.lineTo(well.x + x * cell + 0.5, well.y + well.h);
      ctx.stroke();
    }
    for (y = 0; y <= ROWS; y++) {
      ctx.beginPath();
      ctx.moveTo(well.x, well.y + y * cell + 0.5);
      ctx.lineTo(well.x + well.w, well.y + y * cell + 0.5);
      ctx.stroke();
    }
    for (y = 0; y < ROWS; y++) {
      for (x = 0; x < COLS; x++) {
        var ch = board[y][x];
        if (!ch) continue;
        tile(ctx, well.x + x * cell, well.y + y * cell, cell, INK[ch] || "#ccc", false);
      }
    }
    if (piece && !over) {
      var gy = piece.y;
      while (fits(piece.type, piece.rot, piece.x, gy + 1)) gy += 1;
      if (gy !== piece.y) {
        var ghost = ROTS[piece.type][piece.rot];
        for (i = 0; i < ghost.length; i++) {
          var gx = piece.x + ghost[i][0];
          var gr = gy + ghost[i][1];
          if (gr < 0) continue;
          tile(ctx, well.x + gx * cell, well.y + gr * cell, cell, INK[piece.type], true);
        }
      }
      var live = ROTS[piece.type][piece.rot];
      for (i = 0; i < live.length; i++) {
        var lx = piece.x + live[i][0];
        var ly = piece.y + live[i][1];
        if (ly < 0) continue;
        tile(ctx, well.x + lx * cell, well.y + ly * cell, cell, INK[piece.type], false);
      }
    }
    for (i = 0; i < sparks.length; i++) {
      var sp = sparks[i];
      ctx.globalAlpha = sp.life > 0.4 ? 0.4 : sp.life;
      ctx.fillStyle = sp.color;
      ctx.fillRect(well.x + sp.c * cell, well.y + sp.r * cell, 3, 3);
      ctx.globalAlpha = 1;
    }
    ctx.restore();

    roundRect(ctx, fx, fy, fw, fh, 10);
    ctx.strokeStyle = "rgba(232,206,160,0.72)";
    ctx.lineWidth = 2;
    ctx.stroke();

    drawHold(ctx, m.hold);
    drawNext(ctx, m.next);
    drawHud(ctx, m);
    drawCredit(ctx, m);

    hot.well = { x: well.x, y: well.y, w: well.w, h: well.h };
    hot.restart = m.restart;
    hot.cell = cell;
    hot.card = null;
    if (over) {
      var cw = well.w - 16;
      if (cw < 40) cw = well.w;
      var ch = 86;
      var cx = well.x + (well.w - cw) / 2;
      var cy = well.y + well.h * 0.36;
      roundRect(ctx, cx, cy, cw, ch, 12);
      ctx.fillStyle = "rgba(8,10,20,0.88)";
      ctx.fill();
      ctx.strokeStyle = "rgba(232,206,160,0.55)";
      ctx.lineWidth = 1;
      ctx.stroke();
      ctx.fillStyle = "#f6edd8";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.font = "700 16px " + FONT;
      ctx.fillText("Well is full", cx + cw / 2, cy + 30);
      ctx.font = "12px " + FONT;
      ctx.fillStyle = "rgba(246,237,216,0.8)";
      ctx.fillText("Tap here or the arrow", cx + cw / 2, cy + 56);
      hot.card = { x: cx, y: cy, w: cw, h: ch };
    }
  }

  function notifyReady() {
    if (sent) return;
    var box = window.__gbSandbox;
    if (box && typeof box.ready === "function") {
      sent = true;
      box.ready();
    }
  }

  function boot() {
    var cv = document.getElementById("well");
    var pad = document.getElementById("pad");
    var toggle = document.getElementById("gb-ui-toggle");
    var note = document.getElementById("credit");
    if (!cv || !pad) return;
    var ctx = cv.getContext("2d", { alpha: false }) || cv.getContext("2d");
    if (!ctx) return;

    function viewSize() {
      var rect = cv.getBoundingClientRect();
      var w = rect.width;
      var h = rect.height;
      if (w < 16) w = window.innerWidth || 0;
      if (h < 16) h = window.innerHeight || 0;
      return { w: Math.round(w), h: Math.round(h) };
    }

    function layoutDom(m) {
      var key = m.w + "x" + m.h + ":" + m.btn + ":" + m.gap;
      if (key === laidKey) return;
      laidKey = key;
      pad.style.top = m.padTop + "px";
      pad.style.height = m.btn + "px";
      pad.style.gap = m.gap + "px";
      var buttons = pad.querySelectorAll("button");
      var i;
      for (i = 0; i < buttons.length; i++) {
        buttons[i].style.width = m.btn + "px";
        buttons[i].style.height = m.btn + "px";
      }
      document.body.classList.add("fitted");
    }

    function paint() {
      var sz = viewSize();
      if (sz.w < 16 || sz.h < 16) return false;
      viewW = sz.w;
      viewH = sz.h;
      ensureDust(sz.w, sz.h);
      var m = metrics(sz.w, sz.h);
      layoutDom(m);
      var dpr = window.devicePixelRatio || 1;
      if (dpr > 2) dpr = 2;
      if (dpr < 1) dpr = 1;
      var bw = Math.round(sz.w * dpr);
      var bh = Math.round(sz.h * dpr);
      if (cv.width !== bw || cv.height !== bh) {
        cv.width = bw;
        cv.height = bh;
      }
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      drawScene(ctx, m);
      return true;
    }

    function localPoint(e) {
      var rect = cv.getBoundingClientRect();
      return { x: e.clientX - rect.left, y: e.clientY - rect.top };
    }

    function inside(p, r) {
      if (!r) return false;
      return p.x >= r.x && p.x < r.x + r.w && p.y >= r.y && p.y < r.y + r.h;
    }

    function stop(e) {
      e.stopPropagation();
    }

    function hookToggle(node) {
      if (!node) return;
      node.style.width = "44px";
      node.style.height = "44px";
      var evs = ["pointerdown", "pointerup", "pointermove", "touchstart", "touchend", "mousedown", "mouseup", "wheel"];
      var i;
      for (i = 0; i < evs.length; i++) node.addEventListener(evs[i], stop);
      node.addEventListener("click", function (e) {
        stop(e);
        var on = document.documentElement.classList.toggle("gb-ui-open");
        node.setAttribute("aria-expanded", on ? "true" : "false");
        node.setAttribute("aria-label", on ? "Hide notes" : "Show notes");
      });
    }

    function hookNote(node) {
      if (!node) return;
      var evs = ["pointerdown", "pointerup", "pointermove", "touchstart", "touchend", "touchmove", "wheel"];
      var i;
      for (i = 0; i < evs.length; i++) node.addEventListener(evs[i], stop);
    }

    function hookPad() {
      var buttons = pad.querySelectorAll("button");
      var pointers = {};
      var i;
      for (i = 0; i < buttons.length; i++) {
        (function (btn) {
          var act = btn.getAttribute("data-act");
          btn.addEventListener("pointerdown", function (e) {
            e.preventDefault();
            stop(e);
            try { btn.setPointerCapture(e.pointerId); } catch (err) {}
            pointers[e.pointerId] = act;
            btn.setAttribute("aria-pressed", "true");
            arm();
            if (act === "left" || act === "right") {
              heldActs[act] += 1;
              if (heldActs[act] === 1) {
                pressAct(act);
                repeatAt[act] = performance.now() + 170;
              }
            } else if (act === "soft") {
              softHeld = true;
              pressAct(act);
            } else {
              pressAct(act);
            }
          }, false);
          function release(e) {
            var was = pointers[e.pointerId];
            if (!was) return;
            delete pointers[e.pointerId];
            btn.setAttribute("aria-pressed", "false");
            if (was === "left" || was === "right") {
              heldActs[was] -= 1;
              if (heldActs[was] < 0) heldActs[was] = 0;
            }
            if (was === "soft") {
              var still = false;
              var id;
              for (id in pointers) {
                if (pointers[id] === "soft") still = true;
              }
              if (!still) softHeld = false;
            }
          }
          btn.addEventListener("pointerup", release);
          btn.addEventListener("pointercancel", release);
        })(buttons[i]);
      }
    }

    cv.addEventListener("pointerdown", function (e) {
      if (e.target !== cv) return;
      var p = localPoint(e);
      if (inside(p, hot.restart) || inside(p, hot.card)) {
        e.preventDefault();
        arm();
        bootGame(false);
        paint();
        return;
      }
      if (!inside(p, hot.well)) return;
      e.preventDefault();
      arm();
      gesture = {
        id: e.pointerId,
        sx: p.x,
        sy: p.y,
        steps: 0,
        moved: false
      };
      try { cv.setPointerCapture(e.pointerId); } catch (err) {}
    }, false);

    cv.addEventListener("pointermove", function (e) {
      if (!gesture || gesture.id !== e.pointerId) return;
      var p = localPoint(e);
      var dx = p.x - gesture.sx;
      var dy = p.y - gesture.sy;
      if (dx > 12 || dx < -12 || dy > 12 || dy < -12) gesture.moved = true;
      var cell = hot.cell || 18;
      var want = (dx / cell) | 0;
      while (gesture.steps < want) {
        shift(1);
        gesture.steps += 1;
      }
      while (gesture.steps > want) {
        shift(-1);
        gesture.steps -= 1;
      }
    }, false);

    function endGesture(e) {
      if (!gesture || gesture.id !== e.pointerId) return;
      var p = localPoint(e);
      var dx = p.x - gesture.sx;
      var dy = p.y - gesture.sy;
      var moved = gesture.moved;
      gesture = null;
      if (!moved) turn();
      else if (dy > 42 && dy > (dx < 0 ? -dx : dx)) hardDrop();
    }
    cv.addEventListener("pointerup", endGesture);
    cv.addEventListener("pointercancel", endGesture);
    cv.addEventListener("contextmenu", function (e) { e.preventDefault(); });

    var KEYS = {
      ArrowLeft: "left",
      ArrowRight: "right",
      ArrowDown: "soft",
      ArrowUp: "rot",
      KeyX: "rot",
      KeyZ: "rot",
      Space: "hard",
      KeyH: "hold",
      KeyC: "hold",
      KeyN: "restart"
    };
    window.addEventListener("keydown", function (e) {
      var act = KEYS[e.code];
      if (!act) return;
      e.preventDefault();
      arm();
      if (act === "restart") {
        if (!e.repeat) {
          bootGame(false);
          paint();
        }
        return;
      }
      if (act === "soft") {
        softHeld = true;
        if (!e.repeat) pressAct(act);
        return;
      }
      if (e.repeat && act !== "left" && act !== "right") return;
      pressAct(act);
    });
    window.addEventListener("keyup", function (e) {
      if (e.code === "ArrowDown") softHeld = false;
    });

    window.addEventListener("resize", function () {
      laidKey = "";
      paint();
    });

    hookToggle(toggle);
    hookNote(note);
    hookPad();
    bootGame(true);
    paint();

    function loop(now) {
      if (!paintedOnce) {
        if (paint()) {
          paintedOnce = true;
          lastT = now;
          notifyReady();
        }
      } else {
        var dt = now - lastT;
        if (dt > 48) dt = 48;
        if (dt < 0) dt = 0;
        lastT = now;
        update(dt);
        paint();
        notifyReady();
      }
      window.requestAnimationFrame(loop);
    }
    window.requestAnimationFrame(loop);
  }

  if (typeof document !== "undefined") boot();
})();
