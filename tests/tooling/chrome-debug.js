const fs = require('fs');
const { browser } = require('/home/schorsch/.headed-chrome');
const dir = '/tmp/claude-1000/-home-schorsch/d0785ee2-006f-4d83-9fb1-30d6cfb3c6d2/scratchpad/web';

// decode our own map: [byteOffset, sourceIndex, line, column]
function readMap() {
  const map = JSON.parse(fs.readFileSync(dir + '/prog.wasm.map', 'utf8'));
  const B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
  let g = 0, s = 0, l = 0, c = 0;
  const segs = [];
  for (const seg of map.mappings.split(',')) {
    let v = 0, shift = 0; const nums = [];
    for (const ch of seg) {
      const d = B64.indexOf(ch);
      v |= (d & 31) << shift;
      if (d & 32) shift += 5;
      else { nums.push(v & 1 ? -(v >> 1) : v >> 1); v = 0; shift = 0; }
    }
    if (nums.length === 4) { g += nums[0]; s += nums[1]; l += nums[2]; c += nums[3]; segs.push({ byte: g, source: map.sources[s], line: l, col: c }); }
  }
  return { map, segs };
}

(async () => {
  const { map, segs } = readMap();
  const srcLines = map.sourcesContent[map.sources.indexOf('prog.fpp')].split('\n');
  // the line we want to stop on, found through OUR map
  const want = segs.filter(s => s.source === 'prog.fpp' && srcLines[s.line].includes('let doubled'));
  console.log('map says `let doubled` is at byte offsets:', want.map(w => w.byte).join(','), '(line', (want[0]||{}).line, ')');

  const b = await browser();
  const page = await b.newPage();
  const cdp = await page.target().createCDPSession();
  const requested = [];
  await cdp.send('Network.enable');
  cdp.on('Network.requestWillBeSent', e => requested.push(e.request.url));
  const wasm = new Promise(res => cdp.on('Debugger.scriptParsed', e => { if ((e.url||'').endsWith('.wasm')) res(e); }));
  await cdp.send('Debugger.enable');
  await page.goto('http://localhost:8731/index.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 15000 });
  const script = await wasm;
  console.log('chrome fetched the map:', requested.some(u => u.endsWith('.map')));

  const bp = await cdp.send('Debugger.setBreakpoint', {
    location: { scriptId: script.scriptId, lineNumber: 0, columnNumber: want[0].byte }
  });
  console.log('breakpoint bound at byte', JSON.stringify(bp.actualLocation));

  const paused = new Promise(res => cdp.once('Debugger.paused', res));
  page.evaluate('window.runProgram()').catch(() => {});
  const ev = await Promise.race([paused, new Promise(r => setTimeout(() => r(null), 10000))]);
  if (!ev) { console.log('NO PAUSE'); await page.close(); b.disconnect(); return; }
  const frame = ev.callFrames[0];
  console.log('PAUSED in', frame.functionName, 'at byte', frame.location.columnNumber);
  for (const scope of frame.scopeChain) {
    if (!scope.object || !scope.object.objectId) continue;
    const props = await cdp.send('Runtime.getProperties', { objectId: scope.object.objectId, ownProperties: true });
    const out = [];
    for (const p of props.result) {
      const v = p.value || {};
      let shown = v.description !== undefined ? v.description : JSON.stringify(v.value);
      // a wasm local shows its TYPE at the top level; the value is one level in
      if (v.objectId) {
        const inner = await cdp.send('Runtime.getProperties', { objectId: v.objectId, ownProperties: true });
        const bits = inner.result.map(q => q.name + ':' + (q.value ? (q.value.description ?? JSON.stringify(q.value.value)) : '?'));
        if (bits.length) shown += ' {' + bits.join(', ') + '}';
      }
      out.push(p.name + '=' + shown);
    }
    console.log('  scope', scope.type, ':', out.join(', ').slice(0, 500));
  }
  await cdp.send('Debugger.resume').catch(() => {});
  await page.close();
  b.disconnect();
})().catch(e => { console.error('FAIL', e.message); process.exit(1); });
