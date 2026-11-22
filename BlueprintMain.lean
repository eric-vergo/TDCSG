/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint.PreviewManifest
import TDCSGBlueprint
import TDCSGBlueprint.Figures

open Verso Doc Verso.Genre.Manual

/-- Generate the geometric plates and publish them beside the checked blueprint. -/
def main (args : List String) : IO UInt32 := do
  let figures : System.FilePath := ".lake/build/blueprint-figures"
  let css ← IO.FS.readFile "blueprint/figures.css"
  let js ← IO.FS.readFile "blueprint/verification.js"
  TDCSGBlueprint.Figures.write figures
  Informal.PreviewManifest.blueprintMainWithPreviewData (%doc TDCSGBlueprint) args
    (extensionImpls := by exact extension_impls%)
    (config := { extraFilesHtml := [
                   (figures, "figures"),
                   ("blueprint/notices", "notices"),
                   (".lake/packages/verso/LICENSE", "Apache-2.0.txt"),
                   (".lake/packages/verso/static-web/search/licenses.md", "search-notices.txt"),
                   (".lake/packages/leantex/fonts/newcomputermodern/License.txt", "NewCM-license.txt"),
                   (".lake/packages/leantex/fonts/LPPL-1.3c.txt", "LPPL-1.3c.txt")]
                 extraCss := {⟨css⟩}
                 extraJs := {⟨js⟩} })
    (sideBySide := true)
    (sidebar? := some { links := #[{ label := "Source", href := "https://github.com/eric-vergo/TDCSG" }] })
