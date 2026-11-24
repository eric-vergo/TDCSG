/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra
-/
import VersoBlueprint.PreviewManifest
import PILeanVerso
import TDCSGBlueprint

open Verso Doc Verso.Genre.Manual

/-- Playback uses the same letters and intervals as the checked PILean drawings. The SVG
paths at each stop already contain the endpoints computed by `wordPath`. -/
private def wordMotionData : Lean.Json := Id.run do
  let words := #[1, 2, 3].map fun i => Id.run do
    let letters := (TDCSGFigures.Early.wordPiece i).1.map fun l =>
      Lean.Json.mkObj [("text", Lean.toJson l.text),
        ("left", Lean.toJson (l.centre == TDCSGFigures.leftCentre)),
        ("inverse", Lean.toJson (l.turn == TDCSGFigures.zeta 1))]
    let interval := fun after => Id.run do
      let (a, b) := TDCSGFigures.returnInterval i after
      return #[PILean.Exact.RealValue.toFloat a, PILean.Exact.RealValue.toFloat b]
    return Lean.Json.mkObj [("letters", Lean.toJson letters),
      ("start", Lean.toJson (interval false)), ("landing", Lean.toJson (interval true))]
  return Lean.toJson words

/-- Generate the site: the figures of `TDCSGFigures` through PILean (`PILeanVerso.withFigures`,
with links to Lean declarations into the site itself and source links to the repository), and the
checked blueprint. -/
def main (args : List String) : IO UInt32 := do
  let css ← IO.FS.readFile "blueprint/figures.css"
  let js ← IO.FS.readFile "blueprint/verification.js"
  let motion := "document.addEventListener('DOMContentLoaded', async () => {" ++
    "const figure = document.querySelector('figure[data-lean-decl=\"TDCSGFigures.wordTrace\"]');" ++
    "if (figure) (await import(new URL('word-motion.mjs', document.baseURI))).playWords(figure," ++
    wordMotionData.compress ++ "); });"
  let files : List (System.FilePath × String) := [
    ("blueprint/notices", "notices"),
    ("blueprint/word-motion.mjs", "word-motion.mjs"),
    (".lake/packages/verso/LICENSE", "Apache-2.0.txt"),
    (".lake/packages/verso/static-web/search/licenses.md", "search-notices.txt"),
    (".lake/packages/leantex/fonts/newcomputermodern/License.txt", "NewCM-license.txt"),
    (".lake/packages/leantex/fonts/LPPL-1.3c.txt", "LPPL-1.3c.txt")]
  PILeanVerso.withFigures (%doc TDCSGBlueprint) site_figures% args
    (options := { leanLinks := .site, repo := some "https://github.com/eric-vergo/TDCSG" })
    fun args =>
      Informal.PreviewManifest.blueprintMainWithPreviewData (%doc TDCSGBlueprint) args
        (extensionImpls := by exact extension_impls%)
        (config := { extraFilesHtml := files, extraCss := {⟨css⟩}, extraJs := {⟨js⟩, ⟨motion⟩} })
        (sideBySide := true)
        (sidebar? := some
          { links := #[{ label := "Source", href := "https://github.com/eric-vergo/TDCSG" }] })
