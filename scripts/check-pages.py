"""Verify the rendered blueprint using its GitHub Pages project URL.

The site has two kinds of figures. Hand-drawn plates are SVG files under `plates/`, each the image
of a paragraph that holds its numbered caption, listed in `plates/SHA256SUMS`. Figures drawn by
PILean (`TDCSGFigures`) are `figure.pilean-figure` blocks; the files they show are listed in the
PILean manifest `-verso-data/pilean-figures/manifest.json`, which this check reads instead of a
list of names. For those it requires a visible numbered caption and an accessible name, no active
markup, Lean links that land on an element of an existing page, and it runs PILean's checks:
`pilean-verify` (the folder agrees with its manifest), the site check of PILean's Verso adapter
(every inline picture is the body of a file the manifest lists, with the theme rules the
manifest records) and a fresh render compared with the folder (`--check-figures`, through the
site's generator). Plates and PILean figures share one numbering, 1 to N in document order.
With `--release` it also checks the hosted verification record, the source links at the verified
commit, and that the site's kernel replay accepted every node and calls each judged theorem proved.
"""
import hashlib
import json
import os
import re
import sys
import subprocess
from functools import cache
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit
from xml.etree import ElementTree

site = Path(sys.argv[1]).resolve()
repo_root = Path(__file__).resolve().parent.parent
prefix = "/TDCSG/"
repo_url = "https://github.com/eric-vergo/TDCSG"
origin = "https://eric-vergo.github.io"
figures = set()
captions = {}
linked_declarations = set()
source_links = set()
verification_urls = set()
pages = list(site.rglob("index.html"))
assert site / "index.html" in pages
expected = {n + ".svg" for n in "disks moving lens levels terminal component chord".split()}
plates = site / "plates"
pilean_dir = site / "-verso-data" / "pilean-figures"
pilean_tests = repo_root / ".lake/packages/pilean-verso/verso/example/tests"
# PILean figure blocks: (page, declaration, number, caption text, accessible names, inline
# pictures) in document order within each page.
pilean_figures = []
# Links from PILean figures to Lean declarations in the site: (page, target file, fragment).
pilean_links = set()
# Links from PILean source lines to the repository.
pilean_repo_links = set()
# Active markup found inside a PILean figure or the figures page.
active_markup = []
# Labels each plate must carry, as the text content of its `<text>` elements.
required_labels = {
    "disks.svg": ["a(0)", "72°", "−1", "+1", "r = 1.5", "left disk", "right disk"],
    "chord.svg": ["−E", "E", "piece of word", "parameter t", "t3"],
    "moving.svg": ["window", "r/2", "ζ⁴", "x", "outside the window"],
    "lens.svg": ["lens", "Re v = κ", "Re v = κ − η", "r = 1.8", "|v − u| ≤ r/2"],
    "terminal.svg": ["window", "cut", "n + e0", "r/2", "the level n0 = 4 is good"],
    "levels.svg": ["phase mod L", "level m", "lo = −10", "hi = 3", "good", "not good"],
    "component.svg": ["weight 0", "weight 1", "window", "e0"],
}
# Smallest font size relative to the plate width: a plate is about 330 px wide on a 360 px screen,
# where this ratio renders text at 12 px or more.
min_font_ratio = 0.0375


VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source",
        "track", "wbr"}


class Resources(HTMLParser):
    def __init__(self, url):
        super().__init__()
        self.base = url
        self.anchor = None
        self.source_panels = []
        self.paragraph = None
        self.paragraph_figure = None
        # The open elements of the current PILean figure or figures list, and its record.
        self.pilean = None
        self.pilean_stack = []
        self.part = None
        self.hidden = 0

    def pilean_start(self, tag, attrs, classes):
        """Track a PILean figure block or the figures list, and what is inside it."""
        if not self.pilean_stack:
            if tag == "figure" and "pilean-figure" in classes:
                self.pilean = {"decl": attrs.get("data-lean-decl", ""), "number": None,
                               "text": [], "names": [], "inline": 0}
                pilean_figures.append((page, self.pilean))
            elif not (tag == "div" and "pilean-figure-list" in classes):
                return
            self.pilean_stack = [(tag, False)]
            self.part = None
            return
        if tag == "script":
            active_markup.append(f"{page}: a script element")
        for k, v in attrs.items():
            if k.lower().startswith("on"):
                active_markup.append(f"{page}: the attribute {k}")
            if v and "".join(v.split()).lower().startswith("javascript:"):
                active_markup.append(f"{page}: a script address in {k}")
        fig = self.pilean
        hides = False
        if fig is not None:
            if tag == "span" and "pilean-figure-number" in classes:
                self.part = ("number", len(self.pilean_stack))
            elif tag == "span" and "pilean-figure-text" in classes:
                self.part = ("text", len(self.pilean_stack))
            if tag in ("svg", "math", "style", "title") or "bp_math_source" in classes:
                hides = tag not in VOID
                self.hidden += hides
            if tag == "svg" and "pilean-inline-svg" in classes:
                fig["inline"] += 1
                if attrs.get("role") == "img":
                    fig["names"].append(attrs.get("aria-label", ""))
            if tag == "img":
                fig["names"].append(attrs.get("alt", ""))
            if tag == "a" and "pilean-repo-link" in classes:
                pilean_repo_links.add(attrs.get("href", ""))
        if tag == "a" and {"pilean-decl-link", "pilean-site-link"} & set(classes):
            url = urlsplit(urljoin(self.base, attrs.get("href", "")))
            assert url.hostname == "eric-vergo.github.io" and url.fragment, (page, attrs)
            target = site / unquote(url.path[len(prefix):])
            pilean_links.add((page, target / "index.html" if target.is_dir() else target,
                              unquote(url.fragment)))
        if tag not in VOID:
            self.pilean_stack.append((tag, hides))

    def pilean_end(self, tag):
        if tag not in (t for t, _ in self.pilean_stack):
            return
        while self.pilean_stack:
            open_tag, hid = self.pilean_stack.pop()
            self.hidden -= hid
            if self.part and len(self.pilean_stack) <= self.part[1]:
                self.part = None
            if open_tag == tag:
                break
        if not self.pilean_stack:
            self.pilean, self.part, self.hidden = None, None, 0

    def handle_data(self, data):
        if self.pilean is not None and self.part and self.hidden == 0:
            key = self.part[0]
            if key == "number":
                self.pilean["number"] = (self.pilean["number"] or "") + data
            else:
                self.pilean["text"].append(data)
        self.resource_data(data)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = attrs.get("class", "").split()
        self.pilean_start(tag, attrs, classes)
        # Statement declarations render as `div.bp_decl_source` panels, declarations attached to a
        # proof as `li.bp_external_decl_item` entries; both carry the declaration and its range.
        if tag in ("div", "li"):
            panel = self.source_panels[-1] if self.source_panels else None
            if {"bp_decl_source", "bp_external_decl_item"} & set(classes):
                panel = (attrs["data-lean-decl"], attrs["data-lean-source"])
            self.source_panels.append(panel)
        if tag == "a" and {"bp_decl_source_path", "bp_external_decl_source_path"} & set(classes):
            panel = self.source_panels[-1]
            assert panel, f"Source link outside a Lean declaration panel in {page}"
            source_links.add((*panel, attrs["href"]))
        if tag == "p":
            self.paragraph, self.paragraph_figure = [], None
        if tag == "a" and attrs.get("href"):
            self.anchor = urljoin(self.base, attrs["href"])
        if tag == "base" and attrs.get("href"):
            self.base = urljoin(self.base, attrs["href"])
            return
        linked_declarations.update(attrs.get("data-lean-decls", "").split())
        for key in ("src", "href"):
            value = attrs.get(key)
            if not value or value.startswith("#"):
                continue
            url = urlsplit(urljoin(self.base, value))
            if url.scheme not in ("http", "https") or url.hostname != "eric-vergo.github.io":
                continue
            assert url.path.startswith(prefix), (page, value, url.path)
            target = site / unquote(url.path[len(prefix):])
            if target.is_dir():
                target = target / "index.html"
            assert target.is_file(), (page, value, target)
            if tag == "img" and target.parent == plates:
                assert attrs.get("alt", "").strip(), (page, value)
                assert self.paragraph is not None and self.paragraph_figure is None, \
                    f"{target.name} must open a paragraph of its own, which holds its caption"
                self.paragraph_figure = target.name
                figures.add(target.name)


    def handle_endtag(self, tag):
        self.pilean_end(tag)
        if tag in ("div", "li"):
            self.source_panels.pop()
        if tag == "a":
            self.anchor = None
        if tag == "p" and self.paragraph is not None:
            if self.paragraph_figure:
                text = " ".join("".join(self.paragraph).split())
                match = re.match(r"Figure (\d+)\. (.*)", text)
                assert match and len(match.group(2)) >= 40, \
                    f"{self.paragraph_figure} in {page} needs a visible numbered caption, got {text!r}"
                assert self.paragraph_figure not in captions, self.paragraph_figure
                captions[self.paragraph_figure] = int(match.group(1))
            self.paragraph, self.paragraph_figure = None, None

    def resource_data(self, data):
        if self.paragraph is not None:
            self.paragraph.append(data)
        if data.strip() == "site home" and self.anchor:
            verification_urls.add(urljoin(self.anchor, "verification.json"))


@cache
def source_at(commit, path):
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], text=True).splitlines()


def check_source_links(commit, theorems):
    seen = set()
    for decl, location, href in sorted(source_links):
        match = re.fullmatch(r"([\w/]+\.lean):(\d+):\d+-(\d+):\d+", location)
        assert match, f"Invalid Lean source location for {decl}: {location}"
        path, start, end = match.groups()
        fragment = f"L{start}" if start == end else f"L{start}-L{end}"
        expected_url = f"https://github.com/eric-vergo/TDCSG/blob/{commit}/{path}#{fragment}"
        assert href == expected_url, f"{decl}: expected {expected_url}, got {href}"
        lines = source_at(commit, path)
        assert 1 <= int(start) <= int(end) <= len(lines), f"{decl}: range outside {path}"
        if decl in theorems:
            assert path == "Comparator/Solution.lean", f"{decl}: incorrect solution file {path}"
            name = re.escape(decl.rsplit(".", 1)[-1])
            excerpt = "\n".join(lines[int(start) - 1:int(end)])
            assert re.search(rf"^theorem {name}\b", excerpt, re.MULTILINE), f"{decl}: wrong source range"
        seen.add(decl)
    assert seen == linked_declarations, f"Missing Lean source panels: {linked_declarations - seen}"
    assert set(theorems) <= seen, "Missing independent theorem source links"


for page in pages:
    page_url = origin + prefix + page.relative_to(site).as_posix()
    Resources(page_url).feed(page.read_text())

for decl in ("FiveDisk.finite_iff",):
    assert decl in linked_declarations, f"Missing theorem panel for {decl}"
assert figures == expected, (figures, expected)
assert captions.keys() == expected, captions

# The figures drawn by PILean, against the manifest of the files the site build rendered.
pilean_manifest = json.loads((pilean_dir / "manifest.json").read_text())
assert pilean_manifest["format"] == "pilean-manifest-1", pilean_manifest["format"]
manifest_decls = {entry["decl"] for entry in pilean_manifest["files"]}
assert manifest_decls, "the PILean manifest lists no figure"
shown = [fig["decl"] for _, fig in pilean_figures]
assert set(shown) == manifest_decls, \
    f"figures in the pages {sorted(set(shown))} differ from the manifest's {sorted(manifest_decls)}"
numbers = dict(captions)
inline_pictures = 0
for fig_page, fig in pilean_figures:
    where = f"{fig['decl']} in {fig_page}"
    number = re.fullmatch(r"\s*Figure (\d+)\s*", fig["number"] or "")
    assert number, f"{where} needs a visible figure number, got {fig['number']!r}"
    text = " ".join("".join(fig["text"]).split())
    assert len(text) >= 40, f"{where} needs a visible caption, got {text!r}"
    assert fig["names"] and all(n.strip() for n in fig["names"]), \
        f"{where}: every picture needs an accessible name"
    assert fig["decl"] not in numbers, f"{fig['decl']} is shown twice"
    numbers[fig["decl"]] = int(number.group(1))
    inline_pictures += fig["inline"]
assert sorted(numbers.values()) == list(range(1, len(numbers) + 1)), \
    f"figures and plates must be numbered 1 to {len(numbers)}: {numbers}"
assert not active_markup, active_markup
for link_page, target, fragment in sorted(pilean_links):
    assert target.is_file(), f"{link_page}: a figure links to the missing page {target}"
    assert f'id="{fragment}"' in target.read_text(), \
        f"{link_page}: a figure links to #{fragment}, which {target} does not have"


def run(what, command):
    """Run one of PILean's checks; its output is shown when it fails."""
    done = subprocess.run(command, cwd=repo_root, capture_output=True, text=True)
    assert done.returncode == 0, f"{what} failed:\n{done.stdout}\n{done.stderr}"
    return done.stdout


run("pilean-verify", ["lake", "exe", "pilean-verify", str(pilean_dir)])
out = run("the inline-picture check", ["python3", "-I", str(pilean_tests / "inline_check.py"),
                                         str(site)])
match = re.search(r"(\d+) of (\d+) inline pictures match", out)
assert match and int(match.group(1)) == int(match.group(2)) == inline_pictures > 0, out
out = run("the fresh render (--check-figures)",
          ["lake", "lean", "BlueprintMain.lean", "--", "--run", "BlueprintMain.lean",
           "--check-figures", str(pilean_dir)])
assert re.search(r"^ok: \d+ figure files match$", out, re.MULTILINE), out

manifest = plates / "SHA256SUMS"
checksums = dict(line.split()[::-1] for line in manifest.read_text().splitlines())
assert checksums.keys() == expected
for name, digest in checksums.items():
    data = (manifest.parent / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
    svg = ElementTree.fromstring(data)
    assert svg.tag == "{http://www.w3.org/2000/svg}svg" and len(list(svg.iter())) > 5, name
    ns = "{http://www.w3.org/2000/svg}"
    title = svg.find(ns + "title")
    assert title is not None and title.text and title.text.strip(), f"{name}: missing title"
    plate_width = float(svg.get("viewBox").split()[2])
    texts = list(svg.iter(ns + "text"))
    labels = {"".join(t.itertext()).strip() for t in texts} - {""}
    assert len(labels) >= 4, f"{name}: too few labels"
    for t in texts:
        assert float(t.get("font-size", 0)) >= min_font_ratio * plate_width, \
            f"{name}: label {''.join(t.itertext())!r} too small to read on a narrow screen"
    for want in required_labels[name]:
        assert any(want in text for text in labels), f"{name}: missing label {want!r}"
for name in ("blueprint-manifest.json", "blueprint-html-cache.json"):
    assert (site / "-verso-data" / name).is_file(), name
if "--release" in sys.argv[2:]:
    assert verification_urls == {origin + prefix + "verification.json"}, verification_urls
    record = json.loads((site / "verification.json").read_text())
    assert record["status"] == "passed"
    assert record["commit"] == os.environ["GITHUB_SHA"] and re.fullmatch("[a-f0-9]{40}", record["commit"])
    run_url = f"https://github.com/eric-vergo/TDCSG/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    assert record["run_url"] == run_url and os.environ["GITHUB_RUN_ID"].isdigit()
    assert record["toolchain"] == Path("lean-toolchain").read_text().strip()
    assert record["theorems"] == json.loads(Path("comparator.json").read_text())["theorem_names"]
    assert record["kernels"] == ["Lean kernel"]
    check_source_links(record["commit"], record["theorems"])
    # The site's kernel replay: both checkers of the toolchain (`con-leche`, `con-ron`) accepted
    # an export that covers every node, and the headline calls each judged theorem proved.
    stats = (site / "Project-Stats" / "index.html").read_text()
    state = re.findall(r'class="bp_project_stats[^"]*"[^>]*data-bp-replay-state="(\w+)"', stats)
    assert state == ["accepted"], \
        f"the kernel replay with con-leche and con-ron did not accept the whole site: {state}"
    verdicts = re.findall(r'class="bp_stats_replay_note[^"]*" data-bp-replay="(\w+)"', stats)
    assert verdicts == ["proved"] * len(record["theorems"]), \
        f"the headline does not call every judged theorem proved: {verdicts}"
    # The PILean files and the source lines under the figures name the verified commit.
    for entry in pilean_manifest["files"]:
        assert entry.get("repo") == repo_url and entry.get("commit") == record["commit"], entry
    assert pilean_repo_links, "no PILean figure links its source"
    for href in sorted(pilean_repo_links):
        match = re.fullmatch(re.escape(f"{repo_url}/blob/{record['commit']}/") +
                             r"([\w/]+\.lean)#L(\d+)", href)
        assert match, f"source link {href} does not name the verified commit"
        lines = source_at(record["commit"], match.group(1))
        assert 1 <= int(match.group(2)) <= len(lines), f"{href}: line outside the file"
print(f"Checked {len(pages)} pages, {len(figures)} illustrated plates and "
      f"{len(pilean_figures)} PILean figures ({inline_pictures} inline pictures) under {prefix}.")
