const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', (e && e.stack ? e.stack : String(e)).slice(0, 1200)));
  page.on('console', m => { if (m.type() === 'error') console.log('console:', m.text().slice(0, 200)); });
  await page.goto('http://localhost:8733/worker.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  for (const l of await page.evaluate('window.results')) console.log(l);
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
