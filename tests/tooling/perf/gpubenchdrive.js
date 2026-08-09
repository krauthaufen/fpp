const { browser } = require('/home/schorsch/.headed-chrome');
(async () => {
  const b = await browser();
  const page = await b.newPage();
  await page.setCacheEnabled(false);
  page.on('pageerror', e => console.log('pageerror:', String(e).slice(0, 300)));
  await page.goto('http://localhost:8734/tests/tooling/perf/gpubenchpage.html', { waitUntil: 'load' });
  await page.waitForFunction('window.ready === true', { timeout: 120000 });
  const r = await page.evaluate('window.results');
  await page.close(); b.disconnect();
  if (r.error) { console.error(r.error); process.exit(1); }
  console.log('leg          n        js µs      vm µs   direct µs   ns/op js   vm   direct');
  for (const [leg, d] of Object.entries(r)) {
    const ns = (us) => Math.round(us * 1000 / d.n);
    console.log(
      leg.padEnd(10), String(d.n).padStart(7),
      String(d.js).padStart(9), String(d.vm).padStart(10), String(d.direct).padStart(11),
      String(ns(d.js)).padStart(9), String(ns(d.vm)).padStart(4), String(ns(d.direct)).padStart(8));
  }
})().catch(e => { console.error('FAIL', e.message); process.exit(1); });
