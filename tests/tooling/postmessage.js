const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 160)));
  await page.goto('http://localhost:8731/ping.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  const r = await page.evaluate('window.results');
  console.log('page is cross-origin isolated :', r.crossOriginIsolated, '| SharedArrayBuffer:', r.sharedArrayBuffer, '| Worker:', r.workers);
  console.log('round trip to a worker and back (median of 9):');
  for (const x of r.results)
    console.log('  ' + (x.bytes >= 1048576 ? (x.bytes >> 20) + ' MB' : (x.bytes >> 10) + ' KB').padStart(6) +
                '   copy ' + x.copy.toFixed(2).padStart(7) + ' ms' +
                '   transfer ' + x.transfer.toFixed(3).padStart(7) + ' ms');
  console.log('  structured clone of a 50k-element array: ' + r.objectClone.toFixed(2) + ' ms');
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
