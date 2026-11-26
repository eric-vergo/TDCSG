"""Check the animations of the rendered blueprint in a headless Chromium.

    python3 scripts/check-motion.py SITE EXPECT [SHOTS]

SITE is the generator's `html-multi` folder; EXPECT the folder that `lake exe tdcsg-motion-out
EXPECT` writes from Lean: for each animation of the site, and for its narrow rendition, its
animated SVG, the still of each key, the poster key's PNG, and the exact expectations (at every
rest each actor's anchor in the key's still, every turn with its centre, start, angle and the
eased fraction done at a quarter, a half and three quarters of it, and every actor of every panel
at every rest and three points of every move). SHOTS, if given, is a folder for screenshots.

The checks are PILean's, run on this site:

* `tools/motion-browser-check.py` of the `pilean` package on EXPECT: each animation as a
  standalone file, every rest against its key's still, pixel by pixel and at every actor's anchor
  (0.05 px), true arcs at a quarter, a half and three quarters of every turn, labels and markers
  upright, the panels in phase, reduced motion;
* `motion_browser.py` of the Verso adapter's example checks (`.lake/packages/pilean-verso/verso/
  example/tests`) on the pages of the site that show animations, each served by `browser_check.py`
  under its strict content policy (scripts only from the site's files and the head's inline
  scripts by hash): with the clock paused and set, every actor of each moving picture in the page,
  wide at 1440 px and narrow at 360 px, is where Lean's expectations put it at every rest
  (0.05 px), on its circle at a quarter, a half and three quarters of every turn (0.05 px) at the
  eased angle, labels and markers upright, and the panels in phase; the pictures play; switching
  the theme recolours a moving picture, which moves on; the system's reduced motion,
  `data-motion="reduce"`, the Blueprint's switch and print show the stills with their captions,
  hover and focus the poster key's still in the picture's own box; after each, the picture
  follows its clock again without being sought; ids, captions in the accessibility tree, nothing
  announced, no content-policy report, no console error, the caption's link to the switch, and no
  sideways scrolling at 360, 768 and 1440 px.

This script adds: the hidden states for every animation of a page (PILean's runs them for one),
the positions again in the dark theme, each animation's own page (no console error, no
content-policy report, the table of steps, no sideways scrolling), the width of the figures
against the text column, and that no page carries a script of the site's own for a figure. Every
request that does not go to the local server is refused, so nothing is fetched from elsewhere.
"""
import ast
import json
import os
import re
import subprocess
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
pilean = repo_root / ".lake/packages/pilean"
tests = repo_root / ".lake/packages/pilean-verso/verso/example/tests"
sys.path.insert(0, str(tests))

import browser_check  # noqa: E402
import motion_browser  # noqa: E402
from playwright.sync_api import sync_playwright  # noqa: E402

WIDTHS = [360, 768, 1440]


def motion_pages(site):
    """The pages that show animations, with the number of animations on each, chapters first."""
    found = {}
    for page in sorted(site.rglob("index.html")):
        n = len(re.findall(r'class="pilean-motion[ "]', page.read_text(encoding="utf-8")))
        if n:
            rel = page.parent.relative_to(site).as_posix()
            found[rel + "/" if rel != "." else ""] = n
    return dict(sorted(found.items(), key=lambda kv: kv[0].startswith("Figures/")))


class PageChecks:
    """PILean's checks, with two changes. The count of the motions of a page is taken from the
    page itself: the example's page shows two or more, a chapter here may show one. The control
    of the freeze check (that it notices a picture hidden with `display: none`, which in Chromium
    may stay frozen when shown again) shows that the check can see a freeze where Chromium
    freezes; whether it freezes these pictures varies from run to run (measured: the frame pair
    never, the words sometimes), so the control is printed as a note and does not count. The
    check's power to see a freeze is shown on PILean's own example."""

    controls = []

    def __init__(self, c, count):
        self.c, self.count = c, count

    def check(self, name, ok, detail=""):
        if name.endswith("the page shows its motions inline"):
            ok = len(ast.literal_eval(detail)) == self.count
        if name.endswith("the freeze check notices a picture hidden with display: none"):
            PageChecks.controls.append(ok)
            print(f"{'ok' if ok else 'note'}: {name} {detail}")
            return
        self.c.check(name, ok, detail)

    def section(self, *args):
        self.c.section(*args)


def local_only(new_page):
    """`new_page` whose context refuses every request that does not go to 127.0.0.1."""
    def wrapped(browser, **kw):
        ctx, page = new_page(browser, **kw)
        ctx.route(re.compile(r"^(?!http://127\.0\.0\.1:)"), lambda route: route.abort())
        return ctx, page
    return wrapped


def every_state(c, browser, base, url, label, helpers):
    """The hidden states and the freeze check for every animation of the page but the first, which
    PILean's checks take."""
    ctx, page = helpers["new_page"](browser, viewport={"width": 1440, "height": 900})
    helpers["goto"](page, base + url)
    sids = motion_browser.motion_ids(page)
    ctx.close()
    for sid in sids[1:]:
        motion_browser.state_checks(c, browser, base, url, sid, f"{label} {sid}", helpers, True)


def dark_positions(c, browser, base, url, label, helpers, expect):
    """The positions of every moving picture of the page in the dark theme."""
    ctx, page = helpers["new_page"](browser, viewport={"width": 1440, "height": 900},
                                    color_scheme="dark")
    helpers["goto"](page, base + url)
    dark = page.evaluate("getComputedStyle(document.body).backgroundColor")
    c.check(f"{label}: the dark theme is shown", dark not in ("rgb(255, 255, 255)",), dark)
    for sid in motion_browser.motion_ids(page):
        name = motion_browser.file_of(page, sid)
        with open(os.path.join(expect, name + ".json")) as f:
            spec = json.load(f)
        motion_browser.position_checks(c, page, sid, spec, f"{label} {name} (dark, 1440 px)")
    ctx.close()


def column_checks(c, browser, base, url, label, helpers):
    """The width of each animation against the text column, wide."""
    ctx, page = helpers["new_page"](browser, viewport={"width": 1440, "height": 900})
    helpers["goto"](page, base + url)
    sizes = page.evaluate("""() => [...document.querySelectorAll('figure.pilean-figure')]
      .filter(f => f.querySelector('.pilean-motion')).map(f => {
        const col = f.closest('main').querySelector('p');
        const svg = f.querySelector('svg.pilean-motion-wide');
        return [f.getBoundingClientRect().width, col ? col.getBoundingClientRect().width : 0,
                svg.getBoundingClientRect().width]; })""")
    for fig, col, svg in sizes:
        print(f"{label}: figure {fig:.0f} px, text column {col:.0f} px, picture {svg:.0f} px")
        c.check(f"{label}: the picture fits its figure and the figure the column",
                svg <= fig + 0.5 and fig <= col + 0.5, f"{svg} {fig} {col}")
    ctx.close()


def figure_page_checks(c, browser, base, url, label, helpers, shots):
    """An animation's own page: no console error or policy report, its table of steps and its
    stills, no sideways scrolling."""
    for scheme in ["light", "dark"]:
        for width in WIDTHS:
            ctx, page = helpers["new_page"](browser, viewport={"width": width, "height": 900},
                                            color_scheme=scheme)
            errors = []
            page.on("console", lambda m: errors.append(m.text)
                    if motion_browser.console_error(m) else None)
            helpers["goto"](page, base + url)
            rows = page.evaluate(
                "document.querySelectorAll('table.pilean-motion-steps tbody tr').length")
            keys = page.evaluate("document.querySelectorAll('.pilean-page-motion-key').length")
            wide = page.evaluate("document.documentElement.scrollWidth - window.innerWidth")
            reports = helpers["figure_reports"](page)
            c.check(f"{label} {scheme} {width} px: steps {rows}, stills {keys}, no sideways "
                    "scrolling, no console error, no policy report",
                    rows > 0 and keys == rows + 1 and wide <= 0 and not errors and not reports,
                    f"{wide} px, {errors[:2]}, {reports[:2]}")
            if shots and width in (1440, 390, 360):
                page.screenshot(path=f"{shots}/figure-page-{label}-{scheme}-{width}.png",
                                full_page=True)
            ctx.close()


def shots_of(browser, base, url, label, helpers, shots):
    """Screenshots of a chapter: light and dark at 1440 and 390 px; moving, with animations
    turned off by the switch, and hovered."""
    for scheme in ["light", "dark"]:
        for width in [1440, 390]:
            ctx, page = helpers["new_page"](browser, viewport={"width": width, "height": 900},
                                            color_scheme=scheme)
            helpers["goto"](page, base + url)
            first = page.locator(".pilean-motion-stage").first
            first.scroll_into_view_if_needed()
            page.wait_for_timeout(2600)
            stem = f"{shots}/{label}-{scheme}-{width}"
            page.screenshot(path=f"{stem}-live.png")
            if width == 1440:
                first.hover()
                page.wait_for_timeout(300)
                page.screenshot(path=f"{stem}-hover.png")
                page.mouse.move(2, 2)
            page.evaluate("document.documentElement.setAttribute('data-motion', 'reduce')")
            first.scroll_into_view_if_needed()
            page.wait_for_timeout(300)
            page.screenshot(path=f"{stem}-stills.png")
            ctx.close()


def no_site_scripts(c, site):
    """No page carries a script of this site's own for a figure: no script file for figures but
    PILean's Verso adapter's for its explorers (`pilean-explorer.js`, the sliders that remain),
    and no inline script that names PILean's figures or a player of word animations."""
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
    print(f"script files the pages load: {names}")


STANDALONE = re.compile(
    r"^(?P<name>\S+): rests (?P<rest>\S+) px and \[(?P<pix>[^\]]*)\] pixels off the stills, "
    r"arcs (?P<arc>\S+) px and (?P<deg>\S+) deg, uprights \[(?P<found>[^\]]*)\] of (?P<ups>\d+) "
    r"found, turned (?P<turned>\S+) deg; reduced motion: live hidden 0, poster inline, "
    r"(?P<diff>\S+) of 255 from the poster PNG, switched off again (?P<sw>\d+) pixels off the "
    r"clock \((?P<frozen>\d+) off the time it was hidden\); plays \([^)]*\): (?P<plays>\w+); "
    r"console errors: 0; panels: pixels off their stills (?P<panels>\{[^}]*\}), in phase within "
    r"(?P<phase>\{[^}]*\}) px over \d+ times, 0 pixels outside the panels at 60 times -> "
    r"(?P<verdict>ok|FAILED)$")


def standalone_verdict(line):
    """Whether a result line of PILean's standalone check holds, with one exception: the check
    looks for motion at 0.6 s and 1.8 s, which for these animations is still the first rest (two
    seconds, after the seam's fade in), so its `plays` is false although the picture plays; that
    every moving picture plays is checked on the site instead (`motion_browser.motion_checks`,
    over seven seconds). Every other criterion is read back from the line with PILean's
    tolerances."""
    m = STANDALONE.match(line)
    if not m:
        return None
    if m["verdict"] == "ok":
        return True
    ups = int(m["ups"])
    found = m["found"].replace(" ", "")
    sw, frozen = int(m["sw"]), int(m["frozen"])
    return (float(m["rest"]) <= 0.05 and all(int(x) == 0 for x in m["pix"].split(","))
            and float(m["arc"]) <= 0.05 and float(m["deg"]) <= 0.5
            and found == str(ups) and float(m["turned"]) <= 0.01 and float(m["diff"]) < 8
            and (sw == 0 or sw * 2 < frozen)
            and all(v == 0 for v in ast.literal_eval(m["panels"]).values())
            and all(v <= 0.05 for v in ast.literal_eval(m["phase"]).values()))


def standalone_checks(c, expect):
    """PILean's standalone check on the files of EXPECT, read line by line
    (`standalone_verdict`)."""
    done = subprocess.run([sys.executable, "-I", str(pilean / "tools/motion-browser-check.py"),
                           str(expect)], capture_output=True, text=True)
    print(done.stdout, end="")
    results = [line for line in done.stdout.splitlines() if " -> " in line and ": rests " in line]
    expected = len(list(expect.glob("*.json")))
    c.check("PILean's standalone check ran on every animation and rendition",
            len(results) == expected and "Traceback" not in done.stderr,
            f"{len(results)} of {expected}; {done.stderr[-500:]}")
    for line in results:
        c.check(f"standalone: {line.split(':', 1)[0]}", standalone_verdict(line) is True, line)
    rules = [line for line in done.stdout.splitlines() if line.startswith("pixel rule")]
    c.check("standalone: the pixel rule tells a misplaced shape", rules and
            all(line.endswith("-> ok") for line in rules), str(rules))


def main(argv):
    if len(argv) not in (3, 4):
        print(__doc__)
        return 2
    site, expect = Path(argv[1]).resolve(), Path(argv[2]).resolve()
    shots = argv[3] if len(argv) == 4 else None
    if shots:
        os.makedirs(shots, exist_ok=True)
    c = browser_check.Checks()
    standalone_checks(c, expect)
    no_site_scripts(c, site)
    pages = motion_pages(site)
    print(f"pages with animations: {pages}")
    helpers = {"new_page": local_only(browser_check.new_page), "goto": browser_check.goto,
               "figure_reports": browser_check.figure_reports}
    server, base = browser_check.serve(str(site))
    with sync_playwright() as p:
        browser = p.chromium.launch()
        for url, count in pages.items():
            label = url.strip("/") or "front"
            if url.startswith("Figures/"):
                c.section(f"{label} page", figure_page_checks, c, browser, base, url,
                          label.split("/")[-1], helpers, shots)
                continue
            checks = PageChecks(c, count)
            page_shots = None
            if shots:
                page_shots = os.path.join(shots, label)
                os.makedirs(page_shots, exist_ok=True)
            c.section(f"{label} motions", motion_browser.motion_checks, checks, browser, base, url,
                      label, helpers, str(expect), True, page_shots)
            c.section(f"{label} every motion's states", every_state, c, browser, base, url, label,
                      helpers)
            c.section(f"{label} dark positions", dark_positions, c, browser, base, url, label,
                      helpers, str(expect))
            c.section(f"{label} column", column_checks, c, browser, base, url, label, helpers)
            if shots:
                c.section(f"{label} screenshots", shots_of, browser, base, url, label, helpers,
                          shots)
        browser.close()
    server.shutdown()
    print(f"note: the freeze control saw a freeze on {sum(PageChecks.controls)} of "
          f"{len(PageChecks.controls)} pages")
    print(f"{c.count - c.failed} of {c.count} checks hold")
    return 1 if c.failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
