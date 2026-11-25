"""Verify the rendered blueprint using its GitHub Pages project URL.

Every figure of the site is drawn by PILean (`TDCSGFigures`): a `figure.pilean-figure` block whose
files are listed in the PILean manifest `-verso-data/pilean-figures/manifest.json`, which this
check reads instead of a list of names. For each figure it requires a visible numbered caption and
an accessible name, no active markup, Lean links that land on an element of an existing page, and
the Blueprint's numbering: "Figure k" on the unnumbered pages, "Figure c.k" in chapter c, each
counter running 1, 2, … without gaps or repeats; no page may show any other image than a figure's
own page (`div.pilean-figure-page`) shows of its files. It runs PILean's
checks: `pilean-verify` (the folder agrees with its manifest), the site check of PILean's Verso
adapter (every inline picture is the body of a file the manifest lists, with the theme rules the
manifest records) and a fresh render compared with the folder (`--check-figures`, through the
site's generator).
With `--release` it also checks the hosted verification record, the source links at the verified
commit, and that the site's kernel replay accepted every node and calls each judged theorem proved.
"""
import json
import os
import re
import sys
import subprocess
from functools import cache
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit

site = Path(sys.argv[1]).resolve()
repo_root = Path(__file__).resolve().parent.parent
prefix = "/TDCSG/"
repo_url = "https://github.com/eric-vergo/TDCSG"
origin = "https://eric-vergo.github.io"
repository = "eric-vergo/TDCSG"
# In a release every link to this repository names the verified commit, except these links, which
# are unpinned by nature: the repository home (the sidebar's "Source" link and the Project Stats
# page) and the Actions history (Verification chapter). The run URL of the release is the third
# exception and is added in `check_repository_links`.
unpinned_repository_links = {
    f"https://github.com/{repository}",
    f"https://github.com/{repository}/actions",
}
linked_declarations = set()
# Declarations attached to a proof: the side-by-side layout lists them, with their status, in the
# popover of the node's Lean chip ("Attached to the proof") rather than in a panel of their own.
proof_declarations = set()
attached_to_proof = set()
source_links = set()
repository_links = set()
verification_urls = set()
pages = list(site.rglob("index.html"))
assert site / "index.html" in pages
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
# Images outside PILean figures: (page, address).
other_images = []
# Inline pictures on the figures' own pages (the frames of an explorer).
figure_page_inline = []


VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source",
        "track", "wbr"}


class Resources(HTMLParser):
    def __init__(self, url):
        super().__init__()
        self.base = url
        self.anchor = None
        self.source_panels = []
        # The open elements of the current PILean figure or figures list, and its record.
        self.pilean = None
        self.pilean_stack = []
        self.part = None
        self.hidden = 0
        # The open `div` elements inside a figure's own page (`div.pilean-figure-page`), whose
        # pictures are that figure's files.
        self.figure_page_divs = 0

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
        # An attribute written without a value (`<td class>`) reads as None.
        attrs = {k: v or "" for k, v in attrs}
        classes = attrs["class"].split() if "class" in attrs else []
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
        if tag == "div" and (self.figure_page_divs or "pilean-figure-page" in classes):
            self.figure_page_divs += 1
        if tag == "svg" and self.figure_page_divs and "pilean-inline-svg" in classes:
            figure_page_inline.append(page)
        if tag == "img" and not self.pilean_stack and not self.figure_page_divs:
            other_images.append((page, attrs.get("src", "")))
        if tag == "a" and attrs.get("href"):
            self.anchor = urljoin(self.base, attrs["href"])
        if tag == "base" and attrs.get("href"):
            self.base = urljoin(self.base, attrs["href"])
            return
        decls = attrs.get("data-lean-decls", "").split()
        if attrs.get("data-bp-facet") == "proof":
            proof_declarations.update(decls)
        else:
            linked_declarations.update(decls)
        for key in ("src", "href"):
            value = attrs.get(key)
            if not value or value.startswith("#"):
                continue
            url = urlsplit(urljoin(self.base, value))
            if url.hostname in ("github.com", "www.github.com", "raw.githubusercontent.com"):
                owner_repo = "/".join(url.path.split("/")[1:3]).lower()
                if owner_repo == repository.lower():
                    repository_links.add((page.relative_to(site).as_posix(), url.geturl()))
            if url.scheme not in ("http", "https") or url.hostname != "eric-vergo.github.io":
                continue
            assert url.path.startswith(prefix), (page, value, url.path)
            target = site / unquote(url.path[len(prefix):])
            if target.is_dir():
                target = target / "index.html"
            assert target.is_file(), (page, value, target)

    def handle_endtag(self, tag):
        self.pilean_end(tag)
        if tag == "div" and self.figure_page_divs:
            self.figure_page_divs -= 1
        if tag in ("div", "li"):
            self.source_panels.pop()
        if tag == "a":
            self.anchor = None

    def resource_data(self, data):
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
            assert path == "Comparator/FiveDisk/Solution.lean", f"{decl}: incorrect solution file {path}"
            name = re.escape(decl.rsplit(".", 1)[-1])
            excerpt = "\n".join(lines[int(start) - 1:int(end)])
            assert re.search(rf"^theorem {name}\b", excerpt, re.MULTILINE), f"{decl}: wrong source range"
        seen.add(decl)
    assert seen == linked_declarations, f"Missing Lean source panels: {linked_declarations - seen}"
    assert set(theorems) <= seen, "Missing independent theorem source links"


def check_repository_links(commit, run_id):
    """Every link to this repository is pinned to `commit`, or is one of the listed exceptions."""
    allowed = unpinned_repository_links | {f"https://github.com/{repository}/actions/runs/{run_id}"}
    pinned = re.compile(rf"/{re.escape(repository)}/(blob|tree|raw|blame|commit)/{commit}(/.*)?")
    raw = re.compile(rf"/{re.escape(repository)}/{commit}(/.*)")
    failures = []
    for page, href in sorted(repository_links):
        url = urlsplit(href)
        github = url.scheme == "https" and url.netloc == "github.com"
        if github and not url.query and f"https://github.com{url.path}".rstrip("/") in allowed:
            continue
        if url.scheme == "https" and url.netloc == "raw.githubusercontent.com":
            match = raw.fullmatch(url.path)
        else:
            match = github and pinned.fullmatch(url.path)
        if not match:
            failures.append(f"{page}: {href} is not pinned to the verified commit {commit}")
            continue
        path = unquote((match.groups()[-1] or "").lstrip("/"))
        if path and subprocess.run(["git", "cat-file", "-e", f"{commit}:{path}"],
                                   capture_output=True).returncode != 0:
            failures.append(f"{page}: {href} names {path}, which is not in commit {commit}")
    assert not failures, "\n".join(failures)


attached_list = re.compile(r'<span class="bp_code_hover_label">Attached to the proof</span>'
                           r'<ul class="bp_code_hover_list">(.*?)</ul>', re.S)
for page in pages:
    page_url = origin + prefix + page.relative_to(site).as_posix()
    text = page.read_text()
    Resources(page_url).feed(text)
    for items in attached_list.findall(text):
        attached_to_proof.update(re.findall(r'<span class="bp_code_decl_name"><code>([^<]+)</code>',
                                            items))

missing = proof_declarations - linked_declarations - attached_to_proof
assert not missing, f"declarations of a proof listed nowhere: {sorted(missing)}"

for decl in ("FiveDisk.finite_iff",):
    assert decl in linked_declarations, f"Missing theorem panel for {decl}"
assert not other_images, f"images outside PILean figures: {other_images}"

# The figures drawn by PILean, against the manifest of the files the site build rendered.
pilean_manifest = json.loads((pilean_dir / "manifest.json").read_text())
assert pilean_manifest["format"] == "pilean-manifest-3", pilean_manifest["format"]
manifest_decls = {entry["decl"] for entry in pilean_manifest["files"]}
assert manifest_decls, "the PILean manifest lists no figure"
shown = [fig["decl"] for _, fig in pilean_figures]
assert set(shown) == manifest_decls, \
    f"figures in the pages {sorted(set(shown))} differ from the manifest's {sorted(manifest_decls)}"
numbers = {}
inline_pictures = 0
for fig_page, fig in pilean_figures:
    where = f"{fig['decl']} in {fig_page}"
    number = re.fullmatch(r"\s*Figure (?:(\d+)\.)?(\d+)\s*", fig["number"] or "")
    assert number, f"{where} needs a visible figure number, got {fig['number']!r}"
    text = " ".join("".join(fig["text"]).split())
    assert len(text) >= 40, f"{where} needs a visible caption, got {text!r}"
    assert fig["names"] and all(n.strip() for n in fig["names"]), \
        f"{where}: every picture needs an accessible name"
    assert fig["decl"] not in numbers, f"{fig['decl']} is shown twice"
    numbers[fig["decl"]] = (number.group(1), int(number.group(2)))
    inline_pictures += fig["inline"]
counters = {}
for chapter, k in numbers.values():
    counters.setdefault(chapter, []).append(k)
for chapter, ks in counters.items():
    assert sorted(ks) == list(range(1, len(ks) + 1)), \
        f"the figures {'of chapter ' + chapter if chapter else 'outside chapters'} must be " \
        f"numbered 1 to {len(ks)}: {numbers}"
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
assert match and int(match.group(1)) == int(match.group(2)) == \
    inline_pictures + len(figure_page_inline) and inline_pictures > 0, out
out = run("the fresh render (--check-figures)",
          ["lake", "lean", "BlueprintMain.lean", "--", "--run", "BlueprintMain.lean",
           "--check-figures", str(pilean_dir)])
assert re.search(r"^ok: \d+ figure files match$", out, re.MULTILINE), out

assert not (site / "plates").exists(), "the site has a plates folder; every figure is PILean's"
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
    assert record["theorems"] == json.loads(Path("Comparator/FiveDisk/comparator.json").read_text())["theorem_names"]
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
    check_repository_links(record["commit"], os.environ["GITHUB_RUN_ID"])
print(f"Checked {len(pages)} pages and {len(pilean_figures)} PILean figures "
      f"({inline_pictures} inline pictures) under {prefix}.")
