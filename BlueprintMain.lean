/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint.PreviewManifest
import PILeanVerso
import TDCSGBlueprint
import TDCSGBlueprint.Figures

open Verso Doc Verso.Genre.Manual

/-- Generate the site: the figures of `TDCSGFigures` through PILean (`PILeanVerso.withFigures`,
with links to Lean declarations into the site itself and source links to the repository), the
remaining hand-drawn plates of `TDCSGBlueprint.Figures`, and the checked blueprint. -/
def main (args : List String) : IO UInt32 := do
  let plates : System.FilePath := ".lake/build/blueprint-figures"
  let css ← IO.FS.readFile "blueprint/figures.css"
  let js ← IO.FS.readFile "blueprint/verification.js"
  TDCSGBlueprint.Figures.write plates
  let files : List (System.FilePath × String) := [
    (plates, "plates"),
    ("blueprint/notices", "notices"),
    (".lake/packages/verso/LICENSE", "Apache-2.0.txt"),
    (".lake/packages/verso/static-web/search/licenses.md", "search-notices.txt"),
    (".lake/packages/leantex/fonts/newcomputermodern/License.txt", "NewCM-license.txt"),
    (".lake/packages/leantex/fonts/LPPL-1.3c.txt", "LPPL-1.3c.txt")]
  PILeanVerso.withFigures (%doc TDCSGBlueprint) site_figures% args
    (options := { leanLinks := .site, repo := some "https://github.com/eric-vergo/TDCSG" })
    fun args =>
      Informal.PreviewManifest.blueprintMainWithPreviewData (%doc TDCSGBlueprint) args
        (extensionImpls := by exact extension_impls%)
        (config := { extraFilesHtml := files, extraCss := {⟨css⟩}, extraJs := {⟨js⟩} })
        (sideBySide := true)
        (sidebar? := some
          { links := #[{ label := "Source", href := "https://github.com/eric-vergo/TDCSG" }] })
