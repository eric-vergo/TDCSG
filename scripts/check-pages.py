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
linked_declarations = set()
source_links = set()
verification_urls = set()
pages = list(site.rglob("index.html"))
assert site / "index.html" in pages
expected = {n + ".svg" for n in
            "critical-chord disks moving lens levels terminal component chord".split()}


class Resources(HTMLParser):
    def __init__(self, url):
        super().__init__()
        self.base = url
        self.anchor = None
        self.source_panels = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        classes = attrs.get("class", "").split()
        if tag == "div":
            panel = self.source_panels[-1] if self.source_panels else None
            if "bp_decl_source" in classes:
                panel = (attrs["data-lean-decl"], attrs["data-lean-source"])
            self.source_panels.append(panel)
        if tag == "a" and "bp_decl_source_path" in classes:
            panel = self.source_panels[-1]
            assert panel, f"Source link outside a Lean declaration panel in {page}"
            source_links.add((*panel, attrs["href"]))
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
                figures.add(target.name)


    def handle_endtag(self, tag):
        if tag == "div":
            self.source_panels.pop()
        if tag == "a":
            self.anchor = None

    def handle_data(self, data):
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

for decl in ("FiveDisk.finite_iff", "FiveDisk.infinite_orbit_zero", "FiveDisk.supremum_finite"):
    assert decl in linked_declarations, f"Missing theorem panel for {decl}"
assert figures == expected, (figures, expected)
manifest = site / "figures/SHA256SUMS"
checksums = dict(line.split()[::-1] for line in manifest.read_text().splitlines())
assert checksums.keys() == expected
for name, digest in checksums.items():
    data = (manifest.parent / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
    svg = ElementTree.fromstring(data)
    assert svg.tag == "{http://www.w3.org/2000/svg}svg" and len(list(svg.iter())) > 5, name
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
