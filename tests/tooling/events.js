const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 160)));
  await page.goto('http://localhost:8731/closures.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 15000 });
  const r = await page.evaluate('window.result');
  console.log('closure state after events :', JSON.stringify(r));
  
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
