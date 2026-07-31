const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror', String(e).slice(0, 120)));
  await page.goto('http://localhost:8731/features.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 15000 });
  const f = await page.evaluate('window.features');
  console.log('Chrome ' + (await b.version()));
  for (const [k, v] of Object.entries(f)) console.log('  ' + k.padEnd(20) + ' : ' + v);
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
