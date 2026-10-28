// Relay server for Rust Range room duels.
// It serves the game page, pairs two players by a 4-digit room number, and forwards their messages.
const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PAGE = path.join(__dirname, 'index.html');

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/health') { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  if (url === '/' || url === '/index.html') {
    fs.readFile(PAGE, (err, buf) => {
      if (err) { res.writeHead(500); res.end('index.html missing'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      res.end(buf);
    });
    return;
  }
  res.writeHead(404); res.end('not found');
});

const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 16 * 1024 });
const rooms = new Map(); // code -> { host, guest }

function newCode() {
  for (let i = 0; i < 200; i++) {
    const c = String(1000 + Math.floor(Math.random() * 9000));
    if (!rooms.has(c)) return c;
  }
  return null;
}
function send(ws, obj) { if (ws && ws.readyState === 1) ws.send(JSON.stringify(obj)); }

wss.on('connection', (ws) => {
  ws.isAlive = true;
  ws.room = null;
  ws.peer = null;
  ws.on('pong', () => { ws.isAlive = true; });

  ws.on('message', (data) => {
    const text = data.toString();
    if (ws.peer) { if (ws.peer.readyState === 1) ws.peer.send(text); return; } // paired: just forward
    let m;
    try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || ws.room) return;
    if (m.op === 'create') {
      const code = newCode();
      if (!code) { send(ws, { op: 'error', code: 'busy' }); return; }
      rooms.set(code, { host: ws, guest: null });
      ws.room = code;
      send(ws, { op: 'created', code });
    } else if (m.op === 'join') {
      const room = rooms.get(String(m.code || '').trim());
      if (!room) { send(ws, { op: 'error', code: 'no-room' }); return; }
      if (room.guest) { send(ws, { op: 'error', code: 'full' }); return; }
      room.guest = ws;
      ws.room = String(m.code).trim();
      ws.peer = room.host;
      room.host.peer = ws;
      send(room.host, { op: 'paired', role: 'host' });
      send(ws, { op: 'paired', role: 'guest' });
    }
  });

  ws.on('close', () => {
    const room = ws.room && rooms.get(ws.room);
    if (!room) return;
    const other = room.host === ws ? room.guest : room.host;
    rooms.delete(ws.room);
    if (other) { other.peer = null; other.room = null; send(other, { op: 'peer-left' }); }
  });
});

// drop dead connections, keep idle proxies from closing the sockets
setInterval(() => {
  wss.clients.forEach((ws) => {
    if (!ws.isAlive) { ws.terminate(); return; }
    ws.isAlive = false;
    try { ws.ping(); } catch (e) {}
  });
}, 25000);

server.listen(PORT, () => console.log('Rust Range relay listening on port ' + PORT));
