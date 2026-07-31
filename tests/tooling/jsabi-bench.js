const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 150)));
  await page.goto('http://localhost:8731/bench.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  const r = await page.evaluate('window.results');
  const f = x => x.toFixed(2).padStart(8) + ' ms';
  console.log(`building ${r.N} elements (median of 7):`);
  console.log('  plain JS               ' + f(r.build.plainJs));
  console.log('  wasm, generic ABI      ' + f(r.build.generic) + '   ' + (r.build.generic / r.build.plainJs).toFixed(2) + 'x');
  console.log('  wasm, direct imports   ' + f(r.build.direct)  + '   ' + (r.build.direct  / r.build.plainJs).toFixed(2) + 'x');
  console.log(`property get+set x ${r.LOOPS}:`);
  console.log('  plain JS               ' + f(r.props.plainJs));
  console.log('  wasm, generic ABI      ' + f(r.props.generic) + '   ' + (r.props.generic / r.props.plainJs).toFixed(2) + 'x');
  console.log('  pure wasm loop (floor) ' + f(r.props.pureWasmFloor));
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
