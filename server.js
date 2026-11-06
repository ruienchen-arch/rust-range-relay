// Rust Range relay server — no dependencies, just `node server.js`.
// Serves index.html on "/" and the game relay on the WebSocket path "/ws".
//
// Rooms:
//   {op:'create', max:2}  -> 1v1 duel room (2 seats, sends the old 'paired' message)
//   {op:'create', max:0}  -> co-op room, any number of players (override with env COOP_MAX)
//   {op:'join', code}     -> join a room by its 4-digit code
// The creator is always player id 1 (the host). Every message a player sends is forwarded to
// everybody else in the room with the sender's id added as "i". A message may carry "to": <id>
// to reach one player only (the game uses it for host <-> guest traffic).
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = +process.env.PORT || 8080;
const COOP_MAX = +process.env.COOP_MAX || 0;      // 0 = unlimited
const MAX_MSG = 16 * 1024;                          // the game never sends more than this
const MAX_FRAME = 256 * 1024;
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

const rooms = new Map();

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
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
    if (op === 0x8) { c.close(); return; }
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
  if (!c.room) {                       // first message: create or join
    let m; try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m.op !== 'string') return;
    if (m.op === 'create') {
      const code = newCode();
      if (!code) { c.send(J({ op: 'error', code: 'busy' })); return; }
      const duel = +m.max === 2;
      const room = { code, max: duel ? 2 : COOP_MAX, duel, clients: new Map(), nextId: 1 };
      rooms.set(code, room);
      addClient(room, c);
      c.send(J({ op: 'created', code, id: c.id }));
    } else if (m.op === 'join') {
      const room = rooms.get(String(m.code || '').trim());
      if (!room) { c.send(J({ op: 'error', code: 'no-room' })); return; }
      if (room.max && room.clients.size >= room.max) { c.send(J({ op: 'error', code: 'full' })); return; }
      const peers = [...room.clients.keys()];
      addClient(room, c);
      c.send(J({ op: 'welcome', id: c.id, peers }));
      for (const o of room.clients.values()) if (o !== c) o.send(J({ op: 'peer-joined', id: c.id }));
      if (room.duel) for (const o of room.clients.values()) o.send(J({ op: 'paired' }));
    }
    return;
  }
  if (text.length > MAX_MSG) return;   // oversize: drop
  let m; try { m = JSON.parse(text); } catch (e) { return; }
  if (!m || typeof m !== 'object' || typeof m.t !== 'string') return;
  const to = m.to; delete m.to;
  m.i = c.id;
  const out = J(m);
  const live = m.t === 's' || m.t === 'f' || m.t === 'Ce';
  if (to !== undefined) {
    const o = c.room.clients.get(+to);
    if (o && o !== c) o.send(out, live);
  } else {
    for (const o of c.room.clients.values()) if (o !== c) o.send(out, live);
  }
}
function addClient(room, c) { c.room = room; c.id = room.nextId++; room.clients.set(c.id, c); }

function onClose(c) {
  if (c.closed) return;
  c.closed = true;
  const room = c.room; if (!room) return;
  room.clients.delete(c.id);
  for (const o of room.clients.values()) o.send(J({ op: 'peer-left', id: c.id }));
  if (c.id === 1) {                    // the host left: the room is over
    for (const o of room.clients.values()) o.close();
    rooms.delete(room.code);
  } else if (!room.clients.size) rooms.delete(room.code);
}

// keep connections alive (free hosts drop idle sockets) and clear dead ones
const clientsAll = () => { const l = []; for (const r of rooms.values()) for (const c of r.clients.values()) l.push(c); return l; };
setInterval(() => {
  for (const c of clientsAll()) {
    if (!c.alive) { c.socket.destroy(); continue; }
    c.alive = false;
    try { c.socket.write(frame(0x9, Buffer.alloc(0))); } catch (e) {}
  }
}, 25000).unref();

if (require.main === module) server.listen(PORT, () => console.log('Rust Range relay on :' + PORT));
module.exports = { server, rooms };
