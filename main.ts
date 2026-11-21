// Push-optimal Sokoban solver: BFS over pushes, room by room (see repo history for the long form).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
const CAP = 250000;
function parse(text) {
  const rows = text.split('\n').filter((r) => r.length > 0).map((r) => r.replace(/\r$/, ''));
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1), goals = [], boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x], i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (!x || !y || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}
function liveSq(w, wall, goals) {
  const live = new Uint8Array(wall.length), q = [...goals];
  for (const g of goals) live[g] = 1;
  for (let i = 0; i < q.length; i++) {
    const x = q[i];
    for (const [dx, dy] of D) {
      const d = dy * w + dx, y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) { live[y] = 1; q.push(y); }
    }
  }
  return live;
}
function reach(w, wall, occ, from, seen, stamp, stack) {
  let low = from, n = 0;
  stack[n++] = from; seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (const q of [p - w, p + w, p - 1, p + 1]) if (!wall[q] && !occ[q] && seen[q] !== stamp) { seen[q] = stamp; stack[n++] = q; }
  }
  return low;
}
function frozen(w, wall, occ, goal, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || occ[a]) || !(wall[b] || occ[b]) || !(wall[c] || occ[c]) || !(wall[d] || occ[d])) continue;
    if ((occ[a] && !goal[a]) || (occ[b] && !goal[b]) || (occ[c] && !goal[c]) || (occ[d] && !goal[d])) return true;
  }
  return false;
}
function walkTo(w, wall, occ, from, to) {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1), how = new Array(wall.length), q = [from];
  prev[from] = from;
  for (let i = 0; i < q.length; i++) {
    const p = q[i];
    if (p === to) break;
    for (const [dx, dy, letter] of D) {
      const n = p + dy * w + dx;
      if (wall[n] || occ[n] || prev[n] !== -1) continue;
      prev[n] = p; how[n] = letter; q.push(n);
    }
  }
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}
function solvePush(L) {
  const { w, wall, goals } = L, size = wall.length;
  const goal = new Uint8Array(size), live = liveSq(w, wall, goals), occ = new Uint8Array(size);
  const seen = new Int32Array(size), mark = new Int32Array(size), stack = new Int32Array(size);
  let stamp = 0;
  for (const g of goals) goal[g] = 1;
  const done = (bs) => bs.every((b) => goal[b]);
  if (L.boxes.some((b) => !live[b])) return null;
  const keyOf = (bs, low) => String.fromCharCode(low, ...bs);
  const SB = [L.boxes], SP = [L.player], PA = [-1], index = new Map();
  for (const b of L.boxes) occ[b] = 1;
  index.set(keyOf(L.boxes, reach(w, wall, occ, L.player, seen, ++stamp, stack)), 0);
  for (const b of L.boxes) occ[b] = 0;
  let found = done(L.boxes) ? 0 : -1;
  for (let head = 0; found < 0 && head < SB.length; head++) {
    const boxes = SB[head];
    for (const b of boxes) occ[b] = 1;
    reach(w, wall, occ, SP[head], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || occ[t] || !live[t]) continue;
        occ[b] = 0; occ[t] = 1;
        const fz = frozen(w, wall, occ, goal, t);
        let key = '', next = null;
        if (!fz) {
          next = boxes.slice(); next[bi] = t; next.sort((x, y) => x - y);
          key = keyOf(next, reach(w, wall, occ, b, mark, ++stamp, stack));
        }
        occ[t] = 0; occ[b] = 1;
        if (fz || index.has(key)) continue;
        if (SB.length >= CAP) { for (const x of boxes) occ[x] = 0; return null; }
        index.set(key, SB.length); SB.push(next); SP.push(b); PA.push(head);
        if (done(next)) { found = SB.length - 1; break; }
      }
    }
    for (const x of boxes) occ[x] = 0;
  }
  if (found < 0) return null;
  const path = [];
  for (let s = found; s > 0; s = PA[s]) path.push(s);
  path.reverse();
  let moves = '', player = L.player, boxes = L.boxes;
  for (const s of path) {
    const nb = SB[s], from = boxes.find((b) => !nb.includes(b)), to = nb.find((b) => !boxes.includes(b)), d = to - from;
    const dir = D.find(([dx, dy]) => dy * w + dx === d);
    for (const b of boxes) occ[b] = 1;
    moves += walkTo(w, wall, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += dir[3];
    player = from; boxes = nb;
  }
  return { pushes: path.length, moves };
}
function roomsOf(L) {
  const { w, wall, goals, boxes, player } = L, live = liveSq(w, wall, goals), row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length), part = new Int32Array(wall.length).fill(-1), rooms = [];
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const sq = [s];
    part[s] = rooms.length;
    for (let i = 0; i < sq.length; i++) for (const [dx, dy] of D) {
      const q = sq[i] + dy * w + dx;
      if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rooms.length; sq.push(q); }
    }
    rooms.push({ squares: sq, boxes: [], goals: [], done: false });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}
function solve(text) {
  const L = parse(text);
  if (L.player < 0 || L.boxes.length === 0) return '';
  const rooms = roomsOf(L);
  if (rooms !== null) {
    let player = L.player, moves = '', ok = true;
    for (const room of rooms) {
      const wall = L.wall.slice();
      for (const o of rooms) if (o !== room) for (const c of o.done ? o.goals : o.boxes) wall[c] = 1;
      const sub = { w: L.w, h: L.h, wall, goals: room.goals.slice().sort((a, b) => a - b), boxes: room.boxes.slice().sort((a, b) => a - b), player };
      const s = solvePush(sub);
      if (s === null) { ok = false; break; }
      moves += s.moves;
      for (const ch of s.moves.toLowerCase()) player += ch === 'u' ? -L.w : ch === 'd' ? L.w : ch === 'l' ? -1 : 1;
      room.done = true;
    }
    if (ok) return moves;
  }
  const whole = solvePush(L);
  return whole === null ? '' : whole.moves;
}
for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
