// Released under Apache 2.0. Authors: Eric Vergo, OpenAI Codex.
// Run against a locally served blueprint with playwright-core available to Node.
const assert = require("node:assert/strict");
const { chromium } = require("playwright-core");

async function checkWord(page, index, letters, contacts) {
  const plate = page.locator(".word-plate").nth(index);
  const controls = plate.locator(".word-controls");
  await plate.scrollIntoViewIfNeeded();
  assert.deepEqual(await plate.locator(".word-formula i").allTextContents(), letters);
  const button = name => controls.getByRole("button", {name, exact:true});
  await button("Replay").click();
  await page.clock.runFor(700 + 1240);
  for (let k = 0; k < letters.length; k++) {
    if (k > 0) await page.clock.runFor(1350);
    assert.equal(await plate.locator(".current").textContent(), letters[k]);
    const inverse = letters[k].includes("⁻¹");
    const result = await plate.evaluate((node, {index,k}) => {
      const scene = node.querySelector(".word-scene");
      const path = scene.querySelector(".word-segment");
      const transform = path.transform.baseVal.getItem(0);
      const original = document.querySelectorAll(".word-traces .pilean-explorer-frame")[index];
      const next = [...original.querySelectorAll("g > title")].find(title =>
        title.textContent.startsWith("its image after "+(k+1)+" letters") ||
        title.textContent.startsWith("its image after all "+(k+1)+" letters")).parentNode.querySelector("path");
      const errors = [0,1].map(end => {
        const actual = path.getPointAtLength(end*path.getTotalLength()).matrixTransform(transform.matrix);
        const expected = next.getPointAtLength(end*next.getTotalLength());
        return Math.hypot(actual.x-expected.x, actual.y-expected.y);
      });
      return {angle:transform.angle, active:scene.dataset.active, errors,
        contacts:[...scene.querySelectorAll(".word-contact")].filter(el=>el.style.display!=="none").length};
    }, {index,k});
    assert.equal(result.active,letters[k][0]==="a" ? "left" : "right");
    assert.equal(result.angle,inverse ? -72 : 72);
    assert.ok(result.errors.every(error=>error<0.04), "rotated segment agrees with both checked endpoints");
    assert.equal(result.contacts, contacts.includes(k+1) ? 1 : 0);
  }
  await page.clock.runFor(300);
  assert.equal(await controls.locator("span").textContent(),"Back on the chord");
  assert.ok(await plate.locator(".word-landing").isVisible());
  await page.clock.runFor(1900);
  assert.equal(await plate.locator(".current").textContent(),letters[0]);
  await button("Pause").click();
  const getAngle = () => plate.locator(".word-scene .word-segment").getAttribute("transform");
  const frozen = await getAngle();
  await page.clock.runFor(900);
  assert.equal(await getAngle(),frozen);
  await button("Play").click();
  await page.clock.runFor(950);
  assert.notEqual(await getAngle(),frozen);
  await page.locator("main h1").first().scrollIntoViewIfNeeded();
  await plate.locator(".word-scene").evaluate(scene=>new Promise(resolve=>{
    const observer = new IntersectionObserver(([entry])=>{
      if (!entry.isIntersecting) {
        observer.disconnect();
        resolve();
      }
    });
    observer.observe(scene);
  }));
  await page.clock.runFor(100);
  const offscreen = await getAngle();
  await page.clock.runFor(800);
  assert.equal(await getAngle(),offscreen);
}

async function main() {
  const base = new URL(process.argv[2]);
  const chapter = new URL("The-chord-and-its-three-words/",base);
  const browser = await chromium.launch({executablePath:process.env.CHROMIUM});
  try {
    const page = await browser.newPage({viewport:{width:1280,height:900}});
    const errors = [];
    page.on("pageerror",e=>errors.push(e.message));
    await page.route("**/*",route=>new URL(route.request().url()).origin===base.origin ?
      route.continue() : route.abort());
    await page.clock.install();
    await page.goto(chapter.href);
    await page.locator(".word-plate").first().waitFor();
    assert.equal(await page.locator(".word-plate").count(),3);
    await checkWord(page,0,["a⁻¹","a⁻¹","b⁻¹","a⁻¹","b⁻¹"],[3,4]);
    await checkWord(page,1,["a","b","a","b","b"],[2,3]);
    await checkWord(page,2,["a","b","a","b⁻¹","a⁻¹","b⁻¹"],[1,2,5,6]);
    await page.emulateMedia({reducedMotion:"reduce"});
    await page.clock.runFor(100);
    await page.locator(".word-stills").first().waitFor();
    assert.equal(await page.locator(".word-stills li:visible").count(),16);
    assert.equal(await page.locator(".word-controls:visible").count(),0);
    for (const width of [360,390,1280]) {
      await page.setViewportSize({width,height:850});
      for (const colorScheme of ["dark","light"]) {
        await page.emulateMedia({colorScheme,reducedMotion:"reduce"});
        assert.ok(await page.locator(".word-plate").evaluateAll(nodes=>
          nodes.every(node=>node.scrollWidth<=node.clientWidth+1)));
      }
    }
    const links = page.locator(".word-plate .word-heading a");
    assert.equal(await links.count(),3);
    for (const link of await links.all()) {
      const hash = new URL(await link.evaluate(el=>el.href)).hash;
      assert.ok(await page.evaluate(id=>!!document.getElementById(decodeURIComponent(id)),hash.slice(1)));
    }
    assert.deepEqual(errors,[]);
    const basic = await browser.newPage({javaScriptEnabled:false});
    await basic.goto(chapter.href);
    assert.equal(await basic.locator('[data-lean-decl="TDCSGFigures.wordTrace"] .pilean-explorer-frame:visible').count(),3);
    console.log("All three words, 16 rotations, boundary contacts, landings, controls, links and still views passed.");
  } finally {
    await browser.close();
  }
}

main().catch(error=>{console.error(error);process.exitCode=1;});
