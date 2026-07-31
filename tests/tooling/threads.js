const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 160)));
  await page.goto('http://127.0.0.1:8732/threads.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  const r = await page.evaluate('window.results');
  for (const [k, v] of Object.entries(r)) console.log('  ' + k.padEnd(20) + ': ' + v);
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
