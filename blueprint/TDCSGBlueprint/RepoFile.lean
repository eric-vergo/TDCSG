/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import VersoManual
import VersoBlueprint.Git

/-!
# Links to repository files

The role `{repoFile "notes/engine.md"}[engine guide]` links its text to a file of this repository
at the commit the blueprint is built from. The commit and the GitHub address come from the same
place as the source links of the Lean panels: the `HEAD` commit and the `origin` remote of the Git
checkout that contains the chapter. In the hosted build that checkout is the commit under
verification. Without a Git checkout with a GitHub `origin`, the text is shown without a link, as
the Lean panels show a source path without a link. The file must exist in the checkout.
-/

open Lean Elab Verso Doc Elab ArgParse

namespace TDCSGBlueprint

/-- The arguments of `repoFile`: a path relative to the repository root. -/
structure RepoFileArgs where
  path : String

instance {m} [Monad m] [MonadError m] : FromArgs RepoFileArgs m where
  fromArgs := RepoFileArgs.mk <$> .positional `path (ValDesc.string.as "repository path")

/-- The repository root and the pinned GitHub address of `path`, from the Git checkout that
contains `dir`. -/
def repoFileHref? (dir : System.FilePath) (path : String) :
    IO (Option (System.FilePath × String)) := do
  let some root ← Informal.Git.toplevelAt? dir | return none
  let some info ← Informal.Git.repositoryInfoAtRoot? root | return none
  return some (root, s!"{info.githubUrl}/blob/{info.commit}/{path}")

/-- Link the text to a file of this repository at the commit the blueprint is built from. -/
@[role]
def repoFile : RoleExpanderOf RepoFileArgs
  | {path}, contents => do
    if path.isEmpty || path.startsWith "/" || (path.splitOn "/").contains ".." then
      throwError "repoFile expects a path relative to the repository root, got {path}"
    let content ← contents.mapM elabInline
    let file ← IO.FS.realPath (← getFileName)
    let dir := file.parent.getD "."
    match ← repoFileHref? dir path with
    | some (root, href) =>
      unless ← (root / path).pathExists do
        throwError "repoFile: {path} does not exist in the repository at {root}"
      ``(Verso.Doc.Inline.link #[$content,*] $(quote href))
    | none =>
      ``(Verso.Doc.Inline.concat #[$content,*])

end TDCSGBlueprint
