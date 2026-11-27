"""Check the animations in Firefox and WebKit as well, locally (not in the release workflow).

    python3 scripts/check-engines.py SITE EXPECT [--workers N]

SITE is the generator's `html-multi` folder and EXPECT the folder that `lake exe tdcsg-motion-out
EXPECT` writes, as for `scripts/check-motion.py`, which is the gate and runs in Chromium. This
script runs PILean's checks in the other engines, each only where it can run, and says what it
skipped and why:

* Firefox, on the site: `tools/site/motion_browser.py SITE --expect EXPECT --engine firefox`;
* Firefox, on the standalone files: `tools/motion-browser-check.py EXPECT --engine firefox`;
* WebKit, on the standalone files: `tools/webkit/webkit_check.py EXPECT` (macOS only, with the
  system's `swiftc` and a logged-in session with a screen; it shows nothing and takes no focus).

Run it with the Python of a virtual environment that has Playwright with its Firefox; nothing is
installed or downloaded. Exit status 0 when every pass that ran holds, 1 otherwise.
"""
import importlib.util
import platform
import shutil
import subprocess
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
pilean = repo_root / ".lake/packages/pilean"


def firefox_available():
    """Whether Playwright for this Python can launch its Firefox."""
    if importlib.util.find_spec("playwright") is None:
        return False, "Playwright is not installed for this Python"
    from playwright.sync_api import sync_playwright
    try:
        with sync_playwright() as p:
            p.firefox.launch().close()
        return True, ""
    except Exception as e:  # noqa: BLE001 (any failure to launch means the pass cannot run)
        return False, f"Playwright's Firefox does not launch ({str(e).splitlines()[0]})"


def webkit_available():
    """Whether the WebKit check can run here."""
    if platform.system() != "Darwin":
        return False, "WebKit check needs macOS"
    if shutil.which("swiftc") is None:
        return False, "WebKit check needs the system's swiftc"
    return True, ""


def run(name, command):
    """One pass, by its exit status; its output is shown."""
    print(f"== {name}", flush=True)
    done = subprocess.run(command)
    print(f"== {name}: {'holds' if done.returncode == 0 else 'FAILS'} "
          f"(exit status {done.returncode})", flush=True)
    return done.returncode == 0


def main(argv):
    argv = list(argv)
    workers = []
    if "--workers" in argv:
        i = argv.index("--workers")
        workers = ["--workers", argv[i + 1]]
        del argv[i:i + 2]
    if len(argv) != 3:
        print(__doc__)
        return 2
    site, expect = str(Path(argv[1]).resolve()), str(Path(argv[2]).resolve())
    results, skipped = {}, {}
    ok, why = firefox_available()
    if ok:
        results["Firefox, site"] = run("Firefox, site", [
            sys.executable, "-I", str(pilean / "tools/site/motion_browser.py"), site,
            "--expect", expect, "--engine", "firefox"] + workers)
        results["Firefox, standalone"] = run("Firefox, standalone", [
            sys.executable, "-I", str(pilean / "tools/motion-browser-check.py"), expect,
            "--engine", "firefox"])
    else:
        skipped["Firefox, site"] = skipped["Firefox, standalone"] = why
    ok, why = webkit_available()
    if ok:
        results["WebKit, standalone"] = run("WebKit, standalone", [
            sys.executable, "-I", str(pilean / "tools/webkit/webkit_check.py"), expect])
    else:
        skipped["WebKit, standalone"] = why
    for name, held in results.items():
        print(f"{name}: {'holds' if held else 'FAILS'}")
    for name, why in skipped.items():
        print(f"{name}: skipped, {why}")
    return 0 if all(results.values()) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
