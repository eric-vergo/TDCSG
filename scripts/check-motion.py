"""Check the animations of the rendered blueprint in a headless Chromium.

    python3 scripts/check-motion.py SITE EXPECT [SHOTS] [--workers N]

SITE is the generator's `html-multi` folder; EXPECT the folder that
`lake exe tdcsg-motion-out EXPECT` writes from Lean: for each animation of the site, and for its
narrow rendition, its animated SVG, the still of each key, the poster key's PNG and the exact
expectations (PILean's own writer). SHOTS, if given, is a folder for screenshots. `--workers N`
checks N pages at a time, each in its own Chromium (PILean's `motion_browser.py --workers`).

The checks are PILean's, called on this site:

* `tools/motion-browser-check.py` of the `pilean` package on EXPECT: each animation as a
  standalone file, every rest against its key's still (pixels and every actor's anchor), true arcs
  at a quarter, a half and three quarters of every turn, labels and markers upright, the panels in
  phase, reduced motion, and that the picture plays;
* `tools/site/motion_browser.py` on SITE with EXPECT: every page that shows an animation, served
  under a strict content policy, every moving picture wide and narrow against Lean's
  expectations, every way of turning motion off and hover, focus, click and tap, the picture
  following its clock afterwards (with its freeze control), the theme switched while it moves,
  ids, the accessibility tree, the caption's link and hint, no sideways scrolling, no console
  error and no content-policy report.

Its own checks, of this site: the positions again in the dark theme, each figure no wider than the
text column, every page at 1440, 768, 390 and 320 px without sideways scrolling and with every
formula inside the block that holds it (`formula_checks`, which `scripts/check-engines.py` also
runs in Firefox), no script of the site's own for a figure (the site's scripts are Verso's, Verso
Blueprint's and PILean's explorer script, which PILean's adapter adds to every page with a figure),
and no explorer on any page, so that the explorer script has nothing to run on.
"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
pilean = repo_root / ".lake/packages/pilean"
tools = pilean / "tools/site"
sys.path.insert(0, str(tools))

import motion_browser  # noqa: E402
import site_browser  # noqa: E402
from playwright.sync_api import sync_playwright  # noqa: E402


def run(c, what, command):
    """One of PILean's checks, by its exit status; its output is shown."""
    done = subprocess.run(command, capture_output=True, text=True)
    print(done.stdout, end="")
    print(done.stderr, end="", file=sys.stderr)
    c.check(what, done.returncode == 0, f"exit status {done.returncode}")


def no_site_scripts(c, site):
    """No page carries a script of this site's own for a figure."""
    files, inline = set(), set()
    for page in site.rglob("index.html"):
        text = page.read_text(encoding="utf-8")
        files.update(re.findall(r'<script[^>]*\bsrc="([^"]+)"', text))
        inline.update(re.findall(r"<script(?:\s[^>]*)?>(.*?)</script>", text, re.S))
    names = sorted({f.rsplit("/", 1)[-1] for f in files})
    figure_files = [n for n in names if re.search(r"word|pilean|figure|motion", n, re.I)
                    and n != "pilean-explorer.js"]
    c.check("no script file of the site handles a figure", not figure_files, str(figure_files))
    figure_inline = [b[:80] for b in inline
                     if re.search(r"pilean|word-?motion|playWords|wordTrace", b, re.I)
                     and not b.startswith("window.xref")]
    c.check("no inline script handles a figure", not figure_inline, str(figure_inline[:2]))
    explorers = sorted(str(page.relative_to(site)) for page in site.rglob("index.html")
                       if re.search(r'class="[^"]*\bpilean-explorer\b',
                                    page.read_text(encoding="utf-8")))
    c.check("no page shows an explorer", not explorers, str(explorers[:3]))


def page_checks(c, browser, base, url, expect, helpers):
    """The positions in the dark theme, and the width of each animation against the column."""
    ctx, page = helpers["new_page"](browser, viewport={"width": 1440, "height": 900},
                                    color_scheme="dark")
    helpers["goto"](page, base + url)
    for sid in motion_browser.motion_ids(page):
        name = motion_browser.file_of(page, sid)
        with open(os.path.join(expect, name + ".json")) as f:
            spec = json.load(f)
        motion_browser.position_checks(c, page, sid, spec, f"{url} {name} (dark, 1440 px)")
    sizes = page.evaluate("""() => [...document.querySelectorAll('figure.pilean-figure')]
      .filter(f => f.querySelector('.pilean-motion')).map(f => {
        // the text column: the page's first paragraph outside a figure (on the front page the
        // first paragraph is a figure's caption)
        const p = [...f.closest('main').querySelectorAll('p')].find(q => !q.closest('figure'));
        const col = p ? p.getBoundingClientRect().width : 0;
        return [f.getBoundingClientRect().width, col]; })""")
    for fig, col in sizes:
        print(f"{url}: figure {fig:.0f} px in a text column of {col:.0f} px")
        c.check(f"{url}: the figure fits the text column", fig <= col + 0.5, f"{fig} {col}")
    ctx.close()


# The widths at which every page is checked for its formulas.
FORMULA_WIDTHS = [1440, 768, 390, 320]
# The page's sideways overflow, and the formulas drawn outside the block that holds them (by more
# than 2 px): a
# formula's picture, or a formula's own box where it scrolls sideways (a display formula); with
# the formulas whose picture or hidden MathML copy reaches past the window, which name the cause
# when a page scrolls sideways.
FORMULAS = """() => {
  const vw = document.documentElement.clientWidth, outside = [], past = [];
  for (const f of document.querySelectorAll('.bp_math')) {
    const svg = f.querySelector(':scope > svg');
    if (!svg || !svg.checkVisibility() || !svg.getBoundingClientRect().width) continue;
    const source = (f.querySelector('.bp_math_source') || f).textContent.slice(0, 60);
    const own = ['auto', 'scroll'].includes(getComputedStyle(f).overflowX) ? f : svg;
    let block = f.parentElement;
    while (getComputedStyle(block).display.startsWith('inline')) block = block.parentElement;
    const r = own.getBoundingClientRect(), b = block.getBoundingClientRect();
    // Firefox draws a formula that starts a line up to a pixel before the block's edge.
    if (r.left < b.left - 2 || r.right > b.right + 2) outside.push(source);
    const copy = [...f.querySelectorAll(':scope > math, :scope > math *')];
    const right = Math.max(...[f, svg, ...copy].map(e => e.getBoundingClientRect().right));
    if (right > vw + 0.5) past.push(`${source} (to ${Math.round(right)} px)`);
  }
  return {wide: document.documentElement.scrollWidth - window.innerWidth, outside, past};
}"""


def site_pages(site):
    """The addresses, relative to the site's root, of its pages, without the pages that only send
    the reader on to another address."""
    out = []
    for page in sorted(Path(site).rglob("index.html")):
        if 'http-equiv="refresh"' not in page.read_text(encoding="utf-8"):
            rel = page.parent.relative_to(site).as_posix()
            out.append("" if rel == "." else rel + "/")
    return out


def formula_checks(c, browser, site, base, helpers):
    """Every page of the site at `FORMULA_WIDTHS`: no sideways scrolling, and every formula drawn
    inside the block that holds it."""
    for width in FORMULA_WIDTHS:
        ctx, page = helpers["new_page"](browser, viewport={"width": width, "height": 900})
        for url in site_pages(site):
            helpers["goto"](page, base + url)
            r = page.evaluate(FORMULAS)
            c.check(f"{url or '/'} {width} px: no sideways scrolling", r["wide"] <= 0,
                    f"{r['wide']} px; formulas reaching past the window: {r['past'][:3]}")
            c.check(f"{url or '/'} {width} px: every formula inside its block", not r["outside"],
                    str(r["outside"][:3]))
        ctx.close()


def formula_pass(site, engine):
    """`formula_checks` in the engine `engine` of Playwright; whether every check holds."""
    c = site_browser.Checks()
    helpers = {"new_page": site_browser.new_page, "goto": site_browser.goto}
    server, base = site_browser.serve(str(site))
    with sync_playwright() as p:
        browser = getattr(p, engine).launch()
        c.section(f"formulas of every page ({engine})", formula_checks, c, browser, site, base,
                  helpers)
        browser.close()
    server.shutdown()
    print(f"{c.count - c.failed} of {c.count} checks of the formulas hold ({engine})")
    return c.failed == 0


def main(argv):
    argv = list(argv)
    workers = "1"
    if "--workers" in argv:
        i = argv.index("--workers")
        if i + 1 >= len(argv):
            print(__doc__)
            return 2
        workers = argv[i + 1]
        del argv[i:i + 2]
    if len(argv) not in (3, 4) or not workers.isdigit():
        print(__doc__)
        return 2
    site, expect = Path(argv[1]).resolve(), Path(argv[2]).resolve()
    shots = argv[3] if len(argv) == 4 else None
    c = site_browser.Checks()
    run(c, "PILean's check of the standalone animations",
        [sys.executable, "-I", str(pilean / "tools/motion-browser-check.py"), str(expect)])
    run(c, "PILean's check of the animations in the site's pages",
        [sys.executable, "-I", str(tools / "motion_browser.py"), str(site), "--expect",
         str(expect), "--workers", workers] + (["--shots", shots] if shots else []))
    no_site_scripts(c, site)
    helpers = {"new_page": site_browser.new_page, "goto": site_browser.goto}
    server, base = site_browser.serve(str(site))
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for url in motion_browser.motion_pages(str(site)):
            if not url.startswith("Figures/"):
                c.section(f"{url} dark and column", page_checks, c, browser, base, url,
                          str(expect), helpers)
        c.section("formulas of every page", formula_checks, c, browser, site, base, helpers)
        browser.close()
    server.shutdown()
    print(f"{c.count - c.failed} of {c.count} checks hold")
    return 1 if c.failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
