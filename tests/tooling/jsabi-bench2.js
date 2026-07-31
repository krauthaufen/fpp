const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 150)));
  await page.goto('http://localhost:8731/bench2.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  const r = await page.evaluate('window.results');
  const row = (label, t, crossings) =>
    console.log('  ' + label.padEnd(38) + (t.toFixed(1) + ' ms').padStart(9) +
                '   ' + (t / r.plain).toFixed(1).padStart(5) + 'x vs JS' +
                (crossings ? '   ' + ((t * 1e6 / r.LOOPS) / crossings).toFixed(0) + ' ns/crossing' : ''));
  console.log(`property get+set x ${r.LOOPS}:`);
  row('plain JS', r.plain);
  row('v0 generic, boxed (4 crossings)', r.v0, 4);
  row('v1 generic, typed (2 crossings)', r.v1, 2);
  row('v2 typed + monomorphic accessor (2)', r.v2, 2);
  row('v3 dedicated import per property (2)', r.v3, 2);
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
