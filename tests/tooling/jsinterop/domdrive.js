const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  await page.setCacheEnabled(false);
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 300)));
  await page.goto('http://localhost:8734/tests/tooling/jsinterop/dompage.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 30000 });
  console.log(JSON.stringify(await page.evaluate('window.results')));
  await page.close(); b.disconnect();
})().catch(e => { console.error('FAIL', e.message); process.exit(1); });
