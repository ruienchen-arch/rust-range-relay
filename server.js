// Rust Range relay server — no dependencies, just `node server.js`.
// Serves index.html on "/" and the game relay on the WebSocket path "/ws".
//
// Rooms:
//   {op:'create', max:2}  -> 1v1 duel room (2 seats, sends the old 'paired' message)
//   {op:'create', max:0}  -> co-op room, any number of players (override with env COOP_MAX)
//   {op:'join', code}     -> join a room by its 4-digit code
// Accounts: POST /api/register {user,pass,name} | /api/login {user,pass} | /api/me {token} | /api/name {token,name}
// The wild: player-built parts {t:'Rb'|'Rx'|'Ro'|'Ru'} are checked and stored here (DATA_DIR/world.json) and sent to everybody.
// The creator is always player id 1 (the host). Every message a player sends is forwarded to
// everybody else in the room with the sender's id added as "i". A message may carry "to": <id>
// to reach one player only (the game uses it for host <-> guest traffic).
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = +process.env.PORT || 8080;
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');   // accounts.json lives here
const MAX_ACCOUNTS = 20000;
const TOKEN_DAYS = 30;
const COOP_MAX = +process.env.COOP_MAX || 0;      // 0 = unlimited
const MAX_MSG = 16 * 1024;                          // the game never sends more than this
const MAX_FRAME = 256 * 1024;
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

const rooms = new Map();

// ---------- the permanent shared world ----------
// Everybody who sends {op:'world'} lands in this one room. The oldest connected player is the "authority": the client that
// runs the enemies. The server keeps the state of resource nodes (trees, rocks, ore, crates) and hands out a roster of all
// player positions for the live map. Position and tracer messages only go to players within INTEREST metres (and always
// to the authority, who needs everybody's position to aim its enemies).
const WORLD_SIZE = +process.env.WORLD_SIZE || 1500;
const INTEREST = 420;
const world = { clients: new Map(), nextId: 1, auth: 0, nodes: new Map() };
const RESPAWN_MS = { tree: 600000, rock: 600000, ore: 900000, crate: 900000, hemp: 300000 };
function worldSeed() {
  if (!db.world) { db.world = { seed: buildSeed || playerSeed || ('w' + crypto.randomBytes(4).toString('hex')) }; saveDb(); }   // reuse the island the buildings were made on
  return process.env.WORLD_SEED || db.world.seed;
}
const AUTH_QUIET = 6000;   // the authority's game must send something at least this often (it sends ~20 times a second while playing)
function electAuthority() {
  let best = 0, live = 0; const now = Date.now();
  for (const [id, o] of world.clients) { if (!best || id < best) best = id; if (now - (o.last || 0) < AUTH_QUIET && (!live || id < live)) live = id; }
  if (live) best = live;
  if (best !== world.auth) { world.auth = best; for (const o of world.clients.values()) o.send(JSON.stringify({ op: 'authority', id: best })); }
}
function worldJoin(c, m) {
  checkBuildSeed(); checkPlayerSeed();
  { const u0 = readToken(m.token), g0 = typeof m.gk === 'string' && /^[a-f0-9]{16,64}$/.test(m.gk) ? m.gk : '';
    const ow = u0 ? 'u:' + u0 : g0 ? 'k:' + crypto.createHash('sha256').update(g0).digest('hex').slice(0, 16) : '';
    if (ow) for (const o of [...world.clients.values()]) if (o.owner === ow) { o.close(); onClose(o); }   // back from the lobby: drop the old (maybe half-dead) connection
  }
  const peers = [...world.clients.keys()], names = {};
  for (const o of world.clients.values()) names[o.id] = o.name || '';
  c.world = true; c.room = { code: 'WORLD', duel: false, clients: world.clients }; c.id = world.nextId++; c.x = 0; c.z = 0; c.hasPos = false;
  const user = readToken(m.token), gk = typeof m.gk === 'string' && /^[a-f0-9]{16,64}$/.test(m.gk) ? m.gk : '';
  c.owner = user ? 'u:' + user : gk ? 'k:' + crypto.createHash('sha256').update(gk).digest('hex').slice(0, 16) : 'c:' + c.id;   // who owns what this player builds
  c.name = user ? db.users[user].name : guestName(gk || ('id' + c.id + Date.now()));   // players who are not logged in get a random name (the same one every time in this browser)
  c.last = Date.now();
  world.clients.set(c.id, c);
  const dmg = [];
  for (const [id, n] of world.nodes) dmg.push([id, n.hp]);
  if (!world.auth || !world.clients.has(world.auth) || Date.now() - (world.clients.get(world.auth).last || 0) > AUTH_QUIET) world.auth = c.id;
  c.send(JSON.stringify({ op: 'world-welcome', id: c.id, seed: worldSeed(), size: WORLD_SIZE, name: c.name, peers, names, auth: world.auth, nodes: dmg, me: c.owner, save: c.owner[0] !== 'c' ? players[c.owner] || null : null, chat: chatLog, builds: [...builds.values()].map(pub) }));
  for (const o of world.clients.values()) if (o !== c) o.send(JSON.stringify({ op: 'peer-joined', id: c.id, name: c.name }));
  chatPush({ t: 'RJ', n: c.name, j: 1 });
  electAuthority();
}
// ---- chat and kill feed for the whole world ----
const chatLog = [];   // the last 30 lines, sent to newcomers
function chatPush(o) { chatLog.push(o); if (chatLog.length > 30) chatLog.shift(); worldAll(JSON.stringify(o)); }
const G_ADJ = ['Silent', 'Rusty', 'Wild', 'Lone', 'Swift', 'Grim', 'Lucky', 'Feral', 'Iron', 'Ashen', 'Frozen', 'Sly', 'Brave', 'Hungry', 'Shadow', 'Stone'];
const G_NOUN = ['Wolf', 'Raven', 'Boar', 'Fox', 'Bear', 'Hawk', 'Stag', 'Viper', 'Badger', 'Owl', 'Lynx', 'Crow', 'Moose', 'Otter', 'Hare', 'Shark'];
function guestName(seed) { const h = crypto.createHash('sha256').update('guest:' + seed).digest(); return G_ADJ[h[0] % 16] + G_NOUN[h[1] % 16] + (10 + h[2] % 90); }
function worldChat(c, m) {
  const txt = String(m.m == null ? '' : m.m).replace(/[\u0000-\u001f\u007f]/g, '').replace(/\s+/g, ' ').trim().slice(0, 140);
  if (!txt) return;
  const now = Date.now(); c.ch = (c.ch || []).filter((t) => now - t < 8000);
  if (c.ch.length >= 5) { c.send(JSON.stringify({ t: 'RM', s: 1, m: 'slow' })); return; }
  c.ch.push(now);
  chatPush({ t: 'RM', n: c.name, i: c.id, m: txt });
}
function worldDeath(c, m) {   // the victim reports who or what killed them
  const now = Date.now(); if (now - (c.dt || 0) < 3000) return; c.dt = now;
  const k = world.clients.get(m.a | 0), w = String(m.w || ''), by = String(m.by || '');
  chatPush({ t: 'RK', v: c.name, a: k && k !== c ? k.name : '', w: /^(g[0-9]|rock|hatchet|pickaxe|hammer|hands)$/.test(w) ? w : '', h: m.h ? 1 : 0, by: /^[a-z]{2,8}$/.test(by) ? by : '' });
}
function worldGather(c, m) {
  const id = String(m.id || ''), kind = String(m.k || '');
  if (!/^-?\d+_-?\d+_\d+$/.test(id) || !RESPAWN_MS[kind]) return;
  const max = Math.min(10, Math.max(1, +m.max | 0));
  let n = world.nodes.get(id);
  if (!n) { n = { hp: max, kind, until: 0 }; world.nodes.set(id, n); }
  if (n.hp <= 0) return;
  n.hp -= 1;
  if (n.hp <= 0) n.until = Date.now() + RESPAWN_MS[kind];
  const out = JSON.stringify({ t: 'Rs', id, hp: n.hp });
  for (const o of world.clients.values()) if (o !== c) o.send(out);
}
setInterval(() => {   // trees and rocks grow back, crates get refilled
  const now = Date.now();
  for (const [id, n] of world.nodes) {
    if (n.hp <= 0 && n.until <= now) { world.nodes.delete(id); const out = JSON.stringify({ t: 'Rs', id, hp: -1 }); for (const o of world.clients.values()) o.send(out); }
    else if (n.hp > 0 && (n.last || (n.last = now)) + 300000 < now) { world.nodes.delete(id); }   // partly chopped nodes heal after 5 minutes
  }
}, 5000).unref();
setInterval(() => {   // everybody's position, for the live map
  if (!world.clients.size) return;
  const out = JSON.stringify({ op: 'roster', p: [], n: world.clients.size });   // player positions are not shared on the map
  for (const o of world.clients.values()) o.send(out, true);
}, 1500).unref();

// ---------- accounts (username + password, display name) ----------
// Stored in DATA_DIR/accounts.json. NOTE: free Render instances have a temporary disk, so the file is
// wiped on every redeploy/restart. Attach a Render Disk and set DATA_DIR to its mount path to keep accounts.
const DB_FILE = path.join(DATA_DIR, 'accounts.json');
let db = { secret: crypto.randomBytes(32).toString('hex'), users: {} };
try { db = Object.assign(db, JSON.parse(fs.readFileSync(DB_FILE, 'utf8'))); } catch (e) {}
let saveT = null;
function saveDb() {
  if (saveT) return;
  saveT = setTimeout(() => {
    saveT = null;
    try { fs.mkdirSync(DATA_DIR, { recursive: true }); fs.writeFileSync(DB_FILE + '.tmp', JSON.stringify(db)); fs.renameSync(DB_FILE + '.tmp', DB_FILE); }
    catch (e) { console.error('could not save accounts:', e.message); }
  }, 300);
}
saveDb();   // writes the secret on first start
// ---------- player-built structures in the wild ----------
// Each part is [id, kind, x, y, z, rot, grade, owner, open/lit, hp, extra].
// Building kinds: fd foundation, wl wall, dw doorway, wn window wall, fl floor, st stairs, dr door.
// Deployables: bx storage box, fu furnace, tc tool cupboard, sb sleeping bag.
// extra: tc -> {a:[authorised owners]}, bx -> {s:[18 slots]}, fu -> {s:[fuel, input, frags, cooked], t:tick}.
// Same disk caveat as accounts.json.
const BUILD_FILE = path.join(DATA_DIR, 'world.json');
const BUILD_KINDS = new Set(['fd', 'wl', 'dw', 'wn', 'fl', 'st', 'dr', 'bx', 'fu', 'tc', 'sb',
  'hw', 'lw', 'wf', 'dd', 'rf', 'ft', 'wb', 'sd', 'd2', 'gd', 'xw', 'xs', 'xg', 'wk', 'cf', 'lb', 'bc', 'sk', 'lm', 'bt', 'ln', 'ch', 'tb', 'rg']);
const DOORS = new Set(['dr', 'sd', 'd2', 'gd', 'xg']);                       // open and close, take a code lock
const HOST = { dr: 'dw', sd: 'dw', d2: 'dd', gd: 'wf', wb: 'wn' };          // inserts and the wall they sit in
const CONT = { bx: 18, lb: 30, fu: 4, cf: 4 };                               // containers and their slots
const NO_UP = new Set(['dr', 'sd', 'd2', 'gd', 'wb', 'bx', 'fu', 'tc', 'sb', 'xw', 'xs', 'xg', 'wk', 'cf', 'lb', 'bc', 'sk', 'lm', 'bt', 'ln', 'ch', 'tb', 'rg']);
const HP = { dr: 200, sd: 500, d2: 300, gd: 600, wb: 150, xg: 500, xw: 500, xs: 1500, bx: 150, lb: 300, fu: 300, tc: 300, wk: 300, cf: 100, sb: 60, bc: 300, sk: 250, lm: 50, bt: 100, ln: 100, ch: 100, tb: 100, rg: 50 };
const MAX_BUILDS = +process.env.MAX_BUILDS || 40000, MAX_PER_OWNER = +process.env.MAX_PER_OWNER || 1500;
const TC_RANGE = 25;
const ITEM_RE = /^(wood|stone|metal|frags|cloth|meat|cooked|bandage|satchel|c4|box|furnace|tc|sbag|rock|hatchet|pickaxe|plan|hammer|medkit|armor|adren|ammo|vital|lock|bench|campfire|lbox|barri|spikes|mine|trap|lantern|chair|table|rug|hwall|hswall|hgate|g[0-9])$/;
const builds = new Map();
let buildSeq = 0, buildSeed = '', buildT = null;
function maxHp(k, g) { return HP[k] || [250, 500, 1000][g | 0] || 250; }
function fixRec(a) {   // fill in fields that older saves do not have
  while (a.length < 11) a.push(0);
  if (!(a[9] > 0)) a[9] = maxHp(a[1], a[6]);
  if (a[1] === 'tc' && !(a[10] && Array.isArray(a[10].a))) a[10] = { a: [a[7]] };
  if (CONT[a[1]] && !(a[10] && Array.isArray(a[10].s))) a[10] = { s: new Array(CONT[a[1]]).fill(null), t: 0 };
  return a;
}
const pub = (a) => [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[1] === 'tc' ? a[10] : DOORS.has(a[1]) && a[10] && a[10].c ? { l: 1, a: a[10].a } : 0];   // container contents and lock codes stay on the server
try {
  const w = JSON.parse(fs.readFileSync(BUILD_FILE, 'utf8'));
  buildSeed = String(w.seed || ''); buildSeq = +w.seq || 0;
  (w.b || []).forEach((a) => { if (Array.isArray(a) && a.length >= 9 && BUILD_KINDS.has(a[1])) { builds.set(a[0], fixRec(a)); if (a[0] > buildSeq) buildSeq = a[0]; } });
} catch (e) {}
function writeBuilds() {
  try { fs.mkdirSync(DATA_DIR, { recursive: true }); fs.writeFileSync(BUILD_FILE + '.tmp', JSON.stringify({ seed: buildSeed, seq: buildSeq, b: [...builds.values()] })); fs.renameSync(BUILD_FILE + '.tmp', BUILD_FILE); }
  catch (e) { console.error('could not save buildings:', e.message); }
}
function saveBuilds() { if (!buildT) buildT = setTimeout(() => { buildT = null; writeBuilds(); }, 2000); }
function checkBuildSeed() {   // a new island (new seed) starts with no buildings
  const s = worldSeed();
  if (buildSeed !== s) { if (builds.size) console.log('world seed changed: clearing ' + builds.size + ' building parts'); builds.clear(); buildSeq = 0; buildSeed = s; saveBuilds(); }
}
// ---- each player's backpack, belt, coins and position (DATA_DIR/players.json), so they are still there next visit ----
const PLAYER_FILE = path.join(DATA_DIR, 'players.json');
let players = {}, playerSeed = '', playerT = null;
try { const w = JSON.parse(fs.readFileSync(PLAYER_FILE, 'utf8')); playerSeed = String(w.seed || ''); if (w.p && typeof w.p === 'object') players = w.p; } catch (e) {}
function writePlayers() {
  try { fs.mkdirSync(DATA_DIR, { recursive: true }); fs.writeFileSync(PLAYER_FILE + '.tmp', JSON.stringify({ seed: playerSeed, p: players })); fs.renameSync(PLAYER_FILE + '.tmp', PLAYER_FILE); }
  catch (e) { console.error('could not save players:', e.message); }
}
function savePlayers() { if (!playerT) playerT = setTimeout(() => { playerT = null; writePlayers(); }, 3000); }
function checkPlayerSeed() {   // a new island starts everybody fresh, like a wipe
  const s = worldSeed();
  if (playerSeed !== s) { if (Object.keys(players).length) console.log('world seed changed: clearing saved players'); players = {}; playerSeed = s; savePlayers(); }
}
const int = (v, lo, hi) => (Number.isFinite(+v) ? Math.max(lo, Math.min(hi, Math.round(+v))) : lo);
const num = (v, lim) => (Number.isFinite(+v) && Math.abs(+v) <= lim ? Math.round(+v * 100) / 100 : null);
function cleanSave(s) {
  if (!s || typeof s !== 'object' || !Array.isArray(s.inv) || s.inv.length !== 30) return null;
  const o = { v: 1, t: int(s.t, 0, 9e15), hot: int(s.hot, 0, 5), coins: int(s.coins, 0, 1e9), gr: int(s.gr, 0, 9), inv: [] };
  if (Array.isArray(s.mk)) o.mk = s.mk.filter((m) => Array.isArray(m) && num(m[0], WORLD_SIZE * 2) !== null && num(m[1], WORLD_SIZE * 2) !== null).slice(0, 6).map((m) => [Math.round(+m[0]), Math.round(+m[1])]);   // map markers
  for (const it of s.inv) o.inv.push(Array.isArray(it) && typeof it[0] === 'string' && ITEM_RE.test(it[0]) && +it[1] >= 1 ? [it[0], int(it[1], 1, 100000)] : 0);
  if (s.dead) { o.dead = 1; return o; }
  o.hp = int(s.hp, 1, 1000); o.ar = int(s.ar, 0, 100);
  if (Array.isArray(s.ws) && s.ws.length <= 24) o.ws = s.ws.map((w) => (Array.isArray(w) ? [int(w[0], 0, 1000), int(w[1], 0, 10000)] : [0, 0]));
  const lim = WORLD_SIZE * 2, x = num(s.x, lim), y = num(s.y, 1000), z = num(s.z, lim);
  if (x !== null && y !== null && z !== null) { o.x = x; o.y = y; o.z = z; o.yaw = num(s.yaw, 100) || 0; }
  return o;
}
function worldSave(c, m) {
  if (!c.owner || c.owner[0] === 'c') return;   // no browser key and no account: nothing to tie the save to
  const now = Date.now(); if (c.svT && now - c.svT < 250) return; c.svT = now;
  const s = cleanSave(m.s); if (!s) return;
  players[c.owner] = s; savePlayers();
}
function worldAll(s) { for (const o of world.clients.values()) o.send(s); }
const isWallish = (k) => k === 'wl' || k === 'dw' || k === 'wn' || k === 'hw' || k === 'lw' || k === 'wf' || k === 'dd';
const isFloorish = (k) => k === 'fl' || k === 'rf';
const axisOnly = (k) => isWallish(k) || !!HOST[k] || k === 'xw' || k === 'xs' || k === 'xg';   // only two directions
function authedAt(owner, x, z) {   // false when an unfriendly tool cupboard covers x,z
  for (const a of builds.values()) if (a[1] === 'tc' && Math.hypot(a[2] - x, a[4] - z) < TC_RANGE && a[10].a.indexOf(owner) < 0) return false;
  return true;
}
function coveredBy(owner, x, z) {   // true when a tool cupboard that lists owner covers x,z
  for (const a of builds.values()) if (a[1] === 'tc' && Math.hypot(a[2] - x, a[4] - z) < TC_RANGE && a[10].a.indexOf(owner) >= 0) return true;
  return false;
}
function worldBuild(c, m) {
  const k = String(m.k || ''), x = +m.x, y = +m.y, z = +m.z, r = (m.r | 0) & 3;
  const no = () => c.send(JSON.stringify({ t: 'Rr', k: BUILD_KINDS.has(k) ? k : '' }));
  const now = Date.now();
  c.bh = (c.bh || []).filter((t) => now - t < 10000);
  if (c.bh.length >= 40) return no();                              // at most 40 parts per 10 s
  if (!BUILD_KINDS.has(k) || ![x, y, z].every(Number.isFinite) || Math.abs(x) > WORLD_SIZE || Math.abs(z) > WORLD_SIZE || y < -40 || y > 400) return no();
  if (builds.size >= MAX_BUILDS || !authedAt(c.owner, x, z)) return no();
  let mine = 0;
  for (const a of builds.values()) {
    if (a[7] === c.owner) mine++;
    if (Math.abs(a[2] - x) < 0.25 && Math.abs(a[4] - z) < 0.25 && Math.abs(a[3] - y) < 0.25 && (a[1] === k || (isWallish(k) && isWallish(a[1])) || (HOST[k] && HOST[a[1]] === HOST[k]) || (isFloorish(k) && isFloorish(a[1])))) return no();
  }
  if (mine >= MAX_PER_OWNER) return no();
  c.bh.push(now);
  const R = (v) => Math.round(v * 100) / 100;
  const a = fixRec([++buildSeq, k, R(x), R(y), R(z), axisOnly(k) ? r & 1 : r, 0, c.owner, 0]);
  builds.set(a[0], a); saveBuilds();
  worldAll(JSON.stringify({ t: 'Rb', p: pub(a) }));
}
function dropPart(a, by) {   // a part is gone: doors in a doorway go with it, a destroyed container spills for the raider
  const gone = [a[0]]; builds.delete(a[0]);
  if (Object.values(HOST).indexOf(a[1]) >= 0) for (const b of builds.values()) if (HOST[b[1]] === a[1] && Math.abs(b[2] - a[2]) < 0.25 && Math.abs(b[4] - a[4]) < 0.25 && Math.abs(b[3] - a[3]) < 0.25) { builds.delete(b[0]); gone.push(b[0]); }   // doors and bars go with their wall
  if (by && CONT[a[1]]) { const it = a[10].s.filter(Boolean); if (it.length) by.send(JSON.stringify({ t: 'RD', at: [a[2], a[3], a[4]], it })); }
  saveBuilds();
  gone.forEach((id) => worldAll(JSON.stringify({ t: 'Rx', id })));
  for (const o of world.clients.values()) if (o.open && gone.indexOf(o.open) >= 0) o.open = 0;
}
function worldRemove(c, m) {
  const a = builds.get(m.id | 0); if (!a || a[7] !== c.owner) return;
  if (CONT[a[1]] && a[10].s.some(Boolean)) { c.send(JSON.stringify({ t: 'RN', id: a[0] })); return; }   // empty it first
  dropPart(a, null);
}
function doorOk(c, a) {   // a code lock decides who opens a locked door; otherwise the builder or the tool cupboard
  if (a[10] && a[10].c) return a[10].a.indexOf(c.owner) >= 0;
  return a[7] === c.owner || coveredBy(c.owner, a[2], a[4]);
}
function worldDoor(c, m) {   // doors open and close, lanterns switch, sprung bear traps get re-armed
  const a = builds.get(m.id | 0); if (!a) return;
  if (DOORS.has(a[1])) { if (!doorOk(c, a)) return; }
  else if (a[1] === 'ln') { if (a[7] !== c.owner && !coveredBy(c.owner, a[2], a[4])) return; }
  else if (a[1] === 'bt') { if (!a[8] || (a[7] !== c.owner && !coveredBy(c.owner, a[2], a[4]))) return; }
  else return;
  a[8] = a[8] ? 0 : 1; saveBuilds();
  worldAll(JSON.stringify({ t: 'Ro', id: a[0], o: a[8] }));
}
function near(c, a, d) { return c.hasPos && Math.hypot(c.x - a[2], c.z - a[4]) < d; }
function worldLockSet(c, m) {   // the owner fits a code lock: a new code, only the owner on the list
  const a = builds.get(m.id | 0), code = String(m.code || '');
  if (!a || !DOORS.has(a[1]) || a[7] !== c.owner || !/^\d{4}$/.test(code) || !near(c, a, 10)) { c.send(JSON.stringify({ t: 'RR', it: 'lock', n: 1 })); return; }
  a[10] = { c: code, a: [c.owner] }; saveBuilds();
  worldAll(JSON.stringify({ t: 'RL', id: a[0], l: 1, a: a[10].a }));
}
function worldLockTry(c, m) {   // someone types a code: right adds them and opens the door, wrong gives a shock
  const a = builds.get(m.id | 0); if (!a || !DOORS.has(a[1]) || !(a[10] && a[10].c) || !near(c, a, 10)) return;
  const now = Date.now(); if (now - (c.lockT || 0) < 900) return; c.lockT = now;
  if (String(m.code || '') !== a[10].c) { c.send(JSON.stringify({ t: 'RW', id: a[0] })); return; }
  if (a[10].a.indexOf(c.owner) < 0) a[10].a.push(c.owner);
  a[8] = 1; saveBuilds();
  worldAll(JSON.stringify({ t: 'RL', id: a[0], l: 1, a: a[10].a }));
  worldAll(JSON.stringify({ t: 'Ro', id: a[0], o: 1 }));
}
function worldTrap(c, m) {   // a player stepped on a landmine (it is used up) or a bear trap (it springs)
  const a = builds.get(m.id | 0); if (!a || (a[1] !== 'lm' && a[1] !== 'bt') || a[7] === c.owner || !near(c, a, 12)) return;
  if (a[1] === 'lm') { dropPart(a, null); return; }
  if (a[8]) return;
  a[8] = 1; saveBuilds();
  worldAll(JSON.stringify({ t: 'Ro', id: a[0], o: 1 }));
}
function worldUpgrade(c, m) {
  const a = builds.get(m.id | 0), g = m.g | 0; if (!a || NO_UP.has(a[1]) || a[7] !== c.owner || g < 1 || g > 2 || g <= a[6]) return;
  a[6] = g; a[9] = maxHp(a[1], g); saveBuilds();
  worldAll(JSON.stringify({ t: 'Ru', id: a[0], g }));
}
function worldRepair(c, m) {
  const a = builds.get(m.id | 0); if (!a || (a[7] !== c.owner && !coveredBy(c.owner, a[2], a[4]))) return;
  a[9] = Math.min(maxHp(a[1], a[6]), a[9] + 60); saveBuilds();
  worldAll(JSON.stringify({ t: 'Rp', id: a[0], hp: a[9] }));
}
function worldDamage(c, m) {   // explosions: the thrower reports which parts it hit and how hard
  if (!Array.isArray(m.a) || m.a.length > 60) return;
  const now = Date.now();
  c.dh = (c.dh || []).filter((t) => now - t < 1000);
  if (c.dh.length >= 8) return;
  c.dh.push(now);
  m.a.forEach((q) => {
    if (!Array.isArray(q)) return;
    const a = builds.get(q[0] | 0), d = Math.min(1200, Math.max(0, +q[1] || 0)); if (!a || !d) return;
    a[9] -= d;
    if (a[9] <= 0) dropPart(a, c);
    else { saveBuilds(); worldAll(JSON.stringify({ t: 'Rp', id: a[0], hp: Math.round(a[9]) })); }
  });
}
function worldAuth(c, m) {   // tool cupboard: whoever can reach it can add or remove themselves
  const a = builds.get(m.id | 0); if (!a || a[1] !== 'tc') return;
  const L = a[10].a, i = L.indexOf(c.owner);
  if (i >= 0) L.splice(i, 1); else L.push(c.owner);
  saveBuilds();
  worldAll(JSON.stringify({ t: 'RA', id: a[0], a: L }));
}
// ---- storage boxes and furnaces ----
const FU_IN = { metal: 'frags', meat: 'cooked' };
function contView(c, a) { c.send(JSON.stringify({ t: 'RV', id: a[0], k: a[1], s: a[10].s, lit: a[8] })); }
function contWatchers(a) { for (const o of world.clients.values()) if (o.open === a[0]) contView(o, a); }
const isFurn = (k) => k === 'fu' || k === 'cf';
function contOk(c, a) { return a && CONT[a[1]] && c.hasPos && Math.hypot(c.x - a[2], c.z - a[4]) < 12; }
function worldCont(c, m) {
  const a = builds.get(m.id | 0);
  if (m.t === 'Bc') { c.open = 0; return; }
  if (!contOk(c, a)) { if (m.t === 'Bp') c.send(JSON.stringify({ t: 'RR', it: m.it, n: m.n })); return; }
  const S = a[10].s;
  if (m.t === 'Bq') { c.open = a[0]; contView(c, a); return; }
  if (m.t === 'Bp') {   // put n of an item in
    const it = String(m.it || ''), n0 = Math.min(10000, Math.max(0, m.n | 0)); let n = n0;
    if (!ITEM_RE.test(it) || !n) return;
    if (!isFurn(a[1])) {
      for (let i = 0; i < S.length && n > 0; i++) if (S[i] && S[i][0] === it && S[i][1] < 1000) { const k = Math.min(n, 1000 - S[i][1]); S[i][1] += k; n -= k; }
      for (let i = 0; i < S.length && n > 0; i++) if (!S[i]) { const k = Math.min(n, 1000); S[i] = [it, k]; n -= k; }
    } else {
      const slot = it === 'wood' ? 0 : FU_IN[it] && (a[1] === 'fu' || it === 'meat') ? 1 : -1;   // the campfire only cooks
      if (slot >= 0 && (!S[slot] || S[slot][0] === it)) { const have = S[slot] ? S[slot][1] : 0, k = Math.min(n, 1000 - have); if (k > 0) { S[slot] = [it, have + k]; n -= k; } }
    }
    if (n > 0) c.send(JSON.stringify({ t: 'RR', it, n }));
    if (n < n0) { saveBuilds(); contWatchers(a); }
    return;
  }
  if (m.t === 'Bt') {   // take a whole slot out
    const i = m.s | 0; if (i < 0 || i >= S.length || !S[i]) return;
    const q = S[i]; S[i] = null; saveBuilds();
    c.send(JSON.stringify({ t: 'RG', it: q[0], n: q[1] }));
    contWatchers(a);
    return;
  }
  if (m.t === 'Bl' && isFurn(a[1])) {   // light / put out the furnace
    if (!a[8] && !(S[0] && S[0][1] > 0)) return;
    a[8] = a[8] ? 0 : 1; saveBuilds();
    worldAll(JSON.stringify({ t: 'Rl', id: a[0], o: a[8] }));
    contWatchers(a);
  }
}
setInterval(() => {   // furnaces: 1 ore or raw meat per second, 1 wood every 2 seconds
  for (const a of builds.values()) {
    if (!isFurn(a[1]) || !a[8]) continue;
    const S = a[10].s; a[10].t = (a[10].t || 0) + 1;
    if (S[1] && S[1][1] > 0) {
      const out = FU_IN[S[1][0]], oi = out === 'frags' ? 2 : 3;
      S[1][1]--; if (!S[1][1]) S[1] = null;
      if (S[oi] && S[oi][0] === out) S[oi][1]++; else if (!S[oi]) S[oi] = [out, 1];
    }
    if (a[10].t % 2 === 0 && S[0]) { S[0][1]--; if (!S[0][1]) S[0] = null; }
    if (!S[0]) { a[8] = 0; worldAll(JSON.stringify({ t: 'Rl', id: a[0], o: 0 })); }
    contWatchers(a); saveBuilds();
  }
}, 1000).unref();
function flushOnExit() { if (playerT) { clearTimeout(playerT); playerT = null; writePlayers(); } if (buildT) { clearTimeout(buildT); buildT = null; writeBuilds(); } if (saveT) { clearTimeout(saveT); saveT = null; try { fs.mkdirSync(DATA_DIR, { recursive: true }); fs.writeFileSync(DB_FILE, JSON.stringify(db)); } catch (e) {} } }
process.on('SIGTERM', () => { flushOnExit(); process.exit(0); });
process.on('SIGINT', () => { flushOnExit(); process.exit(0); });

function cleanName(n) {
  return Array.from(String(n == null ? '' : n).replace(/[\u0000-\u001f\u007f<>&"'`\\]/g, '').replace(/\s+/g, ' ').trim()).slice(0, 16).join('');
}
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 32).toString('hex'); }
function sign(p) { return crypto.createHmac('sha256', db.secret).update(p).digest('base64url'); }
function makeToken(user) { const p = Buffer.from(JSON.stringify({ u: user, e: Date.now() + TOKEN_DAYS * 864e5 })).toString('base64url'); return p + '.' + sign(p); }
function readToken(tok) {
  if (typeof tok !== 'string') return null;
  const i = tok.indexOf('.'); if (i < 1) return null;
  const p = tok.slice(0, i), sig = tok.slice(i + 1), want = sign(p);
  if (sig.length !== want.length || !crypto.timingSafeEqual(Buffer.from(sig), Buffer.from(want))) return null;
  try { const o = JSON.parse(Buffer.from(p, 'base64url').toString()); if (o.e < Date.now() || !db.users[o.u]) return null; return o.u; } catch (e) { return null; }
}
const hits = new Map();   // naive per-IP limit on login/register attempts: 25 per 10 minutes
function limited(ip) {
  const now = Date.now(), h = (hits.get(ip) || []).filter(t => now - t < 600000);
  h.push(now); hits.set(ip, h);
  return h.length > 25;
}
setInterval(() => { const now = Date.now(); for (const [k, v] of hits) if (!v.some(t => now - t < 600000)) hits.delete(k); }, 600000).unref();

function api(req, res, url) {
  const send = (code, o) => { res.writeHead(code, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store', 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type' }); res.end(JSON.stringify(o)); };
  if (req.method === 'OPTIONS') return send(204, {});
  if (req.method !== 'POST') return send(405, { error: 'method' });
  let body = '', dead = false;
  req.on('data', (d) => { body += d; if (body.length > 2048 && !dead) { dead = true; send(413, { error: 'too-big' }); req.destroy(); } });
  req.on('end', () => {
    if (dead) return;
    let m; try { m = JSON.parse(body || '{}'); } catch (e) { return send(400, { error: 'bad-json' }); }
    const ip = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
    const user = String(m.user || '').trim().toLowerCase();
    if (url === '/api/register') {
      if (limited(ip)) return send(429, { error: 'rate' });
      if (!/^[a-z0-9_]{3,20}$/.test(user)) return send(400, { error: 'bad-user' });
      const pw = String(m.pass || '');
      if (pw.length < 6 || pw.length > 64) return send(400, { error: 'bad-pass' });
      if (db.users[user]) return send(409, { error: 'taken' });
      if (Object.keys(db.users).length >= MAX_ACCOUNTS) return send(503, { error: 'full' });
      const salt = crypto.randomBytes(16).toString('hex'), name = cleanName(m.name) || user;
      db.users[user] = { salt, hash: hashPw(pw, salt), name, created: Date.now() };
      saveDb();
      return send(200, { token: makeToken(user), user, name });
    }
    if (url === '/api/login') {
      if (limited(ip)) return send(429, { error: 'rate' });
      const u = db.users[user], pw = String(m.pass || '').slice(0, 64);
      const salt = u ? u.salt : '00'.repeat(16), h = hashPw(pw, salt);
      if (!u || h.length !== u.hash.length || !crypto.timingSafeEqual(Buffer.from(h), Buffer.from(u.hash))) return send(401, { error: 'bad-login' });
      return send(200, { token: makeToken(user), user, name: u.name });
    }
    if (url === '/api/me') {
      const who = readToken(m.token); if (!who) return send(401, { error: 'bad-token' });
      return send(200, { user: who, name: db.users[who].name });
    }
    if (url === '/api/name') {
      const who = readToken(m.token); if (!who) return send(401, { error: 'bad-token' });
      const name = cleanName(m.name); if (!name) return send(400, { error: 'bad-name' });
      db.users[who].name = name; saveDb();
      return send(200, { user: who, name });
    }
    send(404, { error: 'not-found' });
  });
}

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/api/world') { res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify({ players: world.clients.size, size: WORLD_SIZE, builds: builds.size })); return; }
  if (url.indexOf('/api/') === 0) { api(req, res, url); return; }
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  if (url === '/' || url === '/index.html') {
    fs.readFile(path.join(__dirname, 'index.html'), (err, buf) => {
      if (err) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('index.html not found next to server.js'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(buf);
    });
    return;
  }
  res.writeHead(404); res.end();
});

// ---------- minimal RFC 6455 ----------
function frame(op, payload) {
  const len = payload.length;
  let head;
  if (len < 126) head = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([head, payload]);
}

server.on('upgrade', (req, socket) => {
  const url = (req.url || '').split('?')[0];
  const key = req.headers['sec-websocket-key'];
  if (url !== '/ws' || !key || (req.headers.upgrade || '').toLowerCase() !== 'websocket') { socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  socket.setNoDelay(true);

  const c = { socket, room: null, id: 0, alive: true, buf: Buffer.alloc(0), frag: [], fragLen: 0, closed: false };
  c.send = (str, droppable) => {
    if (c.closed || socket.destroyed) return;
    if (droppable && socket.writableLength > 1024 * 1024) return;   // slow client: skip live-state messages
    socket.write(frame(0x1, Buffer.from(str)));
  };
  c.close = () => { if (!c.closed) { try { socket.write(frame(0x8, Buffer.alloc(0))); } catch (e) {} socket.end(); } };

  socket.on('data', (d) => {
    c.buf = Buffer.concat([c.buf, d]);
    try { parse(c); } catch (e) { socket.destroy(); }
  });
  socket.on('close', () => onClose(c));
  socket.on('error', () => {});
});

function parse(c) {
  for (;;) {
    const b = c.buf;
    if (b.length < 2) return;
    const fin = (b[0] & 0x80) !== 0, op = b[0] & 0x0f, masked = (b[1] & 0x80) !== 0;
    let len = b[1] & 0x7f, off = 2;
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
    else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10; }
    if (!masked || len > MAX_FRAME) { c.socket.destroy(); return; }
    if (b.length < off + 4 + len) return;
    const mask = b.subarray(off, off + 4);
    const data = Buffer.from(b.subarray(off + 4, off + 4 + len));
    for (let i = 0; i < data.length; i++) data[i] ^= mask[i & 3];
    c.buf = b.subarray(off + 4 + len);
    if (op === 0x8) { c.close(); onClose(c); return; }
    if (op === 0x9) { c.socket.write(frame(0xA, data)); continue; }
    if (op === 0xA) { c.alive = true; continue; }
    if (op === 0x1 || op === 0x0) {
      if (op === 0x1) { c.frag = []; c.fragLen = 0; }
      c.frag.push(data); c.fragLen += data.length;
      if (c.fragLen > MAX_FRAME) { c.socket.destroy(); return; }
      if (fin) { const text = Buffer.concat(c.frag).toString('utf8'); c.frag = []; c.fragLen = 0; onMessage(c, text); }
    }
  }
}

// ---------- rooms ----------
function newCode() {
  for (let i = 0; i < 200; i++) {
    const code = String(1000 + Math.floor(Math.random() * 9000));
    if (!rooms.has(code)) return code;
  }
  return null;
}
const J = (o) => JSON.stringify(o);

function onMessage(c, text) {
  c.last = Date.now();
  if (!c.room) {                       // first message: create or join
    let m; try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m.op !== 'string') return;
    if (m.op === 'world') { worldJoin(c, m); return; }
    if (m.op === 'create') {
      const code = newCode();
      if (!code) { c.send(J({ op: 'error', code: 'busy' })); return; }
      const duel = +m.max === 2;
      const room = { code, max: duel ? 2 : COOP_MAX, duel, clients: new Map(), nextId: 1 };
      rooms.set(code, room);
      addClient(room, c);
      c.name = whoIs(m);
      c.send(J({ op: 'created', code, id: c.id, name: c.name }));
    } else if (m.op === 'join') {
      const room = rooms.get(String(m.code || '').trim());
      if (!room) { c.send(J({ op: 'error', code: 'no-room' })); return; }
      if (room.max && room.clients.size >= room.max) { c.send(J({ op: 'error', code: 'full' })); return; }
      const peers = [...room.clients.keys()], names = {};
      for (const o of room.clients.values()) names[o.id] = o.name || '';
      addClient(room, c);
      c.name = whoIs(m);
      c.send(J({ op: 'welcome', id: c.id, peers, names, name: c.name }));
      for (const o of room.clients.values()) if (o !== c) o.send(J({ op: 'peer-joined', id: c.id, name: c.name }));
      if (room.duel) for (const o of room.clients.values()) o.send(J({ op: 'paired' }));
    }
    return;
  }
  if (text.length > MAX_MSG) return;   // oversize: drop
  let m; try { m = JSON.parse(text); } catch (e) { return; }
  if (!m || typeof m !== 'object' || typeof m.t !== 'string') return;
  if (c.world && m.t === 'Rg') { worldGather(c, m); return; }
  if (c.world && m.t === 'Rb') { worldBuild(c, m); return; }
  if (c.world && m.t === 'Rx') { worldRemove(c, m); return; }
  if (c.world && m.t === 'Ro') { worldDoor(c, m); return; }
  if (c.world && m.t === 'Ru') { worldUpgrade(c, m); return; }
  if (c.world && m.t === 'Rq') { worldRepair(c, m); return; }
  if (c.world && m.t === 'Rm') { worldChat(c, m); return; }
  if (c.world && m.t === 'Re') { worldDeath(c, m); return; }
  if (c.world && m.t === 'Rh') { worldDamage(c, m); return; }
  if (c.world && m.t === 'Ra') { worldAuth(c, m); return; }
  if (c.world && m.t === 'Rz') { worldLockSet(c, m); return; }
  if (c.world && m.t === 'Ry') { worldLockTry(c, m); return; }
  if (c.world && m.t === 'Rt') { worldTrap(c, m); return; }
  if (c.world && m.t === 'Rs') { worldSave(c, m); return; }
  if (c.world && (m.t === 'Bq' || m.t === 'Bp' || m.t === 'Bt' || m.t === 'Bl' || m.t === 'Bc')) { worldCont(c, m); return; }
  const to = m.to; delete m.to;
  m.i = c.id;
  const out = J(m);
  const live = m.t === 's' || m.t === 'f' || m.t === 'Ce';
  if (c.world && (m.t === 's' || m.t === 'f') && to === undefined) {   // area of interest
    if (m.t === 's' && isFinite(m.x) && isFinite(m.z)) { c.x = +m.x; c.z = +m.z; c.hasPos = true; }
    for (const o of world.clients.values()) {
      if (o === c) continue;
      if (o.id !== world.auth && o.hasPos && c.hasPos && Math.hypot(o.x - c.x, o.z - c.z) > INTEREST) continue;
      o.send(out, true);
    }
    return;
  }
  if (to !== undefined) {
    const o = c.room.clients.get(+to);
    if (o && o !== c) o.send(out, live);
  } else {
    for (const o of c.room.clients.values()) if (o !== c) o.send(out, live);
  }
}
// a verified account name when a valid token came with the message, otherwise the (cleaned) guest name
function whoIs(m) { const u = readToken(m.token); return u ? db.users[u].name : cleanName(m.name); }
function addClient(room, c) { c.room = room; c.id = room.nextId++; room.clients.set(c.id, c); }

function onClose(c) {
  if (c.closed) return;
  c.closed = true;
  const room = c.room; if (!room) return;
  room.clients.delete(c.id);
  for (const o of room.clients.values()) o.send(J({ op: 'peer-left', id: c.id }));
  if (c.world) { chatPush({ t: 'RJ', n: c.name, j: 0 }); if (c.id === world.auth) { world.auth = 0; electAuthority(); } return; }
  if (c.id === 1) {                    // the host left: the room is over
    for (const o of room.clients.values()) o.close();
    rooms.delete(room.code);
  } else if (!room.clients.size) rooms.delete(room.code);
}

// keep connections alive (free hosts drop idle sockets) and clear dead ones
const clientsAll = () => { const l = [...world.clients.values()]; for (const r of rooms.values()) for (const c of r.clients.values()) l.push(c); return l; };   // the wild too (it used to be missed)
setInterval(() => {   // the authority went quiet (closed tab, lost connection, hidden tab): hand spawning to someone who is playing
  const a = world.clients.get(world.auth);
  if (world.clients.size && (!a || Date.now() - (a.last || 0) > AUTH_QUIET)) electAuthority();
}, 2000).unref();
setInterval(() => {
  for (const c of clientsAll()) {
    if (!c.alive) { c.socket.destroy(); continue; }
    c.alive = false;
    try { c.socket.write(frame(0x9, Buffer.alloc(0))); } catch (e) {}
  }
}, 25000).unref();

if (require.main === module) server.listen(PORT, () => console.log('Rust Range relay on :' + PORT));
module.exports = { server, rooms, builds };
