const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 150)));
  await page.goto('http://localhost:8731/imports.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 60000 });
  const rs = await page.evaluate('window.results');
  console.log('imports   module      build glue   compile   instantiate');
  for (const r of rs)
    console.log(String(r.n).padStart(6) + '  ' + (r.bytes/1024).toFixed(1).padStart(7) + ' KB' +
                (r.glueMs.toFixed(2) + ' ms').padStart(12) +
                (r.compile.toFixed(2) + ' ms').padStart(11) +
                (r.instantiate.toFixed(2) + ' ms').padStart(13));
  await page.close(); b.disconnect();
})().catch(e => console.error('FAIL', e.message));
