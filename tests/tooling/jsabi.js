const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 160)));
  await page.goto('http://localhost:8731/jsabi.html', { waitUntil: 'load' });
  try { await page.waitForFunction('window.ready === true', { timeout: 10000 }); }
  catch { console.log('did not finish'); await page.close(); b.disconnect(); return; }
  console.log('element built:', (await page.evaluate('window.before')).html);
  console.log('clicks before:', (await page.evaluate('window.before')).clicks,
              '-> after two JS clicks:', (await page.evaluate('window.after')).clicks);
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
