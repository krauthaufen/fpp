const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  const errs = [];
  page.on('pageerror', e => errs.push(String(e)));
  await page.goto('http://localhost:8731/dom.html', { waitUntil: 'load' });
  try { await page.waitForFunction('window.ready === true', { timeout: 10000 }); }
  catch (e) { console.log('FAILED:', errs.join(' | ') || 'timeout'); await page.close(); b.disconnect(); return; }
  console.log('DOM after wasm ran:', await page.evaluate('window.result'));
  await page.close();
  b.disconnect();
})().catch(e => console.error('FAIL', e.message));
