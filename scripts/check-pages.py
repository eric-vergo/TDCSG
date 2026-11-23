"""Verify the rendered blueprint using its GitHub Pages project URL."""
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
prefix = "/TDCSG/"
origin = "https://eric-vergo.github.io"
figures = set()
captions = {}
linked_declarations = set()
source_links = set()
verification_urls = set()
pages = list(site.rglob("index.html"))
assert site / "index.html" in pages
expected = {n + ".svg" for n in
            "critical-chord disks moving lens levels terminal component chord".split()}
# Labels each plate must carry, as the text content of its `<text>` elements.
required_labels = {
    "critical-chord.svg": ["−E", "E", "−1", "+1", "R = √(3 + φ)", "left disk", "right disk"],
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


class Resources(HTMLParser):
    def __init__(self, url):
        super().__init__()
        self.base = url
        self.anchor = None
        self.source_panels = []
        self.paragraph = None
        self.paragraph_figure = None

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = attrs.get("class", "").split()
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
            if tag == "img" and target.parent == site / "figures":
                assert attrs.get("alt", "").strip(), (page, value)
                assert self.paragraph is not None and self.paragraph_figure is None, \
                    f"{target.name} must open a paragraph of its own, which holds its caption"
                self.paragraph_figure = target.name
                figures.add(target.name)


    def handle_endtag(self, tag):
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

    def handle_data(self, data):
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
assert sorted(captions.values()) == list(range(1, len(expected) + 1)), captions
manifest = site / "figures/SHA256SUMS"
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
print(f"Checked {len(pages)} pages and {len(figures)} illustrated plates under {prefix}.")
