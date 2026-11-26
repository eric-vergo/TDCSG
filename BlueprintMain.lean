/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint.PreviewManifest
import PILeanVerso
import TDCSGBlueprint

open Verso Doc Verso.Genre.Manual

/-- Figure pages of earlier versions of the site and the pages of the figures that replaced them:
`(old declaration, new declaration)`. -/
def movedFigures : List (String × String) :=
  [("TDCSGFigures.wordTrace", "TDCSGFigures.wordLoop1"),
    ("TDCSGFigures.Lift.changeOfFrame", "TDCSGFigures.Lift.framePair")]

/-- A page at `Figures/<old>/` that sends the reader to `Figures/<new>/`: a refresh without script
and a link, so that addresses of earlier versions of the site keep working. -/
def movedPage (old new : String) : String :=
  s!"<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><title>{old}</title>" ++
    s!"<meta http-equiv=\"refresh\" content=\"0; url=../{new}/\">" ++
    s!"<link rel=\"canonical\" href=\"../{new}/\"></head><body><p>This figure is now " ++
    s!"<a href=\"../{new}/\">{new}</a>.</p></body></html>\n"

/-- Generate the site: the figures of `TDCSGFigures` through PILean (`PILeanVerso.withFigures`,
with links to Lean declarations into the site itself and source links to the repository), and the
checked blueprint; then the pages of figures that moved (`movedFigures`). -/
def main (args : List String) : IO UInt32 := do
  let css ← IO.FS.readFile "blueprint/figures.css"
  let js ← IO.FS.readFile "blueprint/verification.js"
  let files : List (System.FilePath × String) := [
    ("blueprint/notices", "notices"),
    (".lake/packages/verso/LICENSE", "Apache-2.0.txt"),
    (".lake/packages/verso/static-web/search/licenses.md", "search-notices.txt"),
    (".lake/packages/leantex/fonts/newcomputermodern/License.txt", "NewCM-license.txt"),
    (".lake/packages/leantex/fonts/LPPL-1.3c.txt", "LPPL-1.3c.txt")]
  let code ← PILeanVerso.withFigures (%doc TDCSGBlueprint) site_figures% args
    (options := { leanLinks := .site, repo := some "https://github.com/eric-vergo/TDCSG" })
    fun doc args =>
      Informal.PreviewManifest.blueprintMainWithPreviewData doc args
        (extensionImpls := by exact extension_impls%)
        (config := { extraFilesHtml := files, extraCss := {⟨css⟩}, extraJs := {⟨js⟩} })
        (sideBySide := true)
        (sidebar? := some
          { links := #[{ label := "Source", href := "https://github.com/eric-vergo/TDCSG" }] })
  if code == 0 then
    for (old, new) in movedFigures do
      let dir := PILeanVerso.outputDir args / "html-multi" / "Figures" / old
      if !(← System.FilePath.pathExists dir) then
        IO.FS.createDirAll dir
        IO.FS.writeFile (dir / "index.html") (movedPage old new)
  return code
