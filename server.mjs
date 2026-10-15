import http from 'node:http';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
const root = path.join(path.dirname(fileURLToPath(import.meta.url)), 'dist');
const port = Number(process.env.PORT || 4173);
const host = process.env.HOST || '127.0.0.1';
const types = {'.html':'text/html; charset=utf-8','.css':'text/css; charset=utf-8','.js':'text/javascript; charset=utf-8','.json':'application/json; charset=utf-8','.pdf':'application/pdf','.zip':'application/zip','.lean':'text/plain; charset=utf-8','.md':'text/plain; charset=utf-8','.svg':'image/svg+xml','.jpg':'image/jpeg','.png':'image/png','.woff2':'font/woff2','.ttf':'font/ttf'};
http.createServer(async (req,res) => {
  try {
    const url=new URL(req.url,'http://127.0.0.1');
    const relative=decodeURIComponent(url.pathname).replace(/^\/+/, '') || 'index.html';
    const file=path.resolve(root,relative);
    if(!file.startsWith(root+path.sep)) { res.writeHead(403);res.end('Forbidden');return; }
    const body=await fs.readFile(file);
    res.writeHead(200,{'Content-Type':types[path.extname(file)]||'application/octet-stream','Cache-Control':'no-cache'});res.end(body);
  } catch {res.writeHead(404);res.end('Not found');}
}).listen(port,host,()=>console.log(`Portfolio: http://${host}:${port}`));
