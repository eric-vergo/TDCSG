/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5.5
-/
import TDCSGFigures.Data.Frames

/-!
# Words for the frame pair of chapter 4

A search, by exact computation, over the words in `a` and `b` applied to `z = 0` at `r = 1.95`,
for words to show in the two frames of chapter 4 (`TDCSGFigures.Lift.statesFor`). It is not part
of any build; run it from the repository root with

```sh
lake env lean scripts/FrameWords.lean
```

It prints the report (`TDCSGFigures.Lift.wordReport`) of the chosen words, then

* the closed words (the last state is the first: same point, label and direction index) of at most
  `maxLen` letters with at least one letter that does not act, shortest first, both with any
  letters acting and with both `a` and `b` acting at least once, each with its idle positions and
  its extent in both frames;
* the words of 6 to 8 letters with exactly one letter that does not act, neither the first nor the
  last, `a` and `b` both acting, smallest extent first.

Every decision is exact (`ℤ[ζ₅]`, `ℚ(√5)`); the decimals are for reading.
-/

open TDCSGFigures TDCSGFigures.Lift TDCSGFigures.Early PILean.Exact

/-- `r² = 1.95²`. -/
def r2 : QSqrt5 := rat (39 / 20 * (39 / 20))

/-- The longest word searched. -/
def maxLen : Nat := 14

/-- A word met by the search, with what the search tracked along it. -/
structure Row where
  /-- The word. -/
  w : List Letter
  /-- Whether its last state is its first. -/
  closed : Bool
  /-- The positions, from `1`, of the letters that do not act. -/
  idle : List Nat
  /-- How many `a` act. -/
  actsA : Nat
  /-- How many `b` act. -/
  actsB : Nat
  /-- The largest `|(y + 1)/2|²` along the word. -/
  halvedSq : QSqrt5
  /-- The largest `|P - x|²` of a left or right centre along the word. -/
  centreSq : QSqrt5

/-- The larger squared extent of a row, over both frames. -/
def Row.extent (r : Row) : QSqrt5 := qMax r.halvedSq r.centreSq

/-- `|(y + 1)/2|²` and the larger `|P - x|²` of the two centres of a state, for `z = 0`. -/
def reach (s : State) : QSqrt5 × QSqrt5 :=
  ((s.y + Zeta5.ofInt 1).normSq * rat (1 / 4),
    qMax (windowDistSq4 origin s.n * rat (1 / 4)) (windowDistSq4 origin s.rightLabel * rat (1 / 4)))

/-- Every word of at most `len` letters in `a` and `b` that extends `w` (reversed), depth first,
with the tracked data. -/
partial def search (len : Nat) (s : State) (w : List Letter) (idle : List Nat) (na nb : Nat)
    (h c : QSqrt5) (acc : Array Row) : Array Row := Id.run do
  let mut acc := acc
  if !w.isEmpty then
    let closed := s.y == origin && s.n == zeroLabel && s.j % 5 == 0
    acc := acc.push ⟨w.reverse, closed, idle.reverse, na, nb, h, c⟩
  if w.length < len then
    for l in [Letter.a, Letter.b] do
      let t := s.applyAt r2 l
      let (h', c') := reach t
      let k := w.length + 1
      let (idle', na', nb') :=
        if !t.acted then (k :: idle, na, nb) else if l == .a then (idle, na + 1, nb)
        else (idle, na, nb + 1)
      acc := search len t (l :: w) idle' na' nb' (qMax h h') (qMax c c') acc
  return acc

/-- The decimal of `√q`. -/
def dec (q : QSqrt5) : String := decimalText (⟨q⟩ : SqrtOf QSqrt5) 3

/-- A row as one line of text. -/
def Row.text (r : Row) : String :=
  s!"{wordText r.w} ({r.w.length} letters): idle at {r.idle}; closes {r.closed}; " ++
    s!"largest |(y + 1)/2| ≈ {dec r.halvedSq}, largest |P − x| ≈ {dec r.centreSq}"

/-- Sorts rows by length, then by extent. -/
def byLength (rs : Array Row) : Array Row :=
  rs.qsort fun x y => x.w.length < y.w.length ||
    (x.w.length == y.w.length && QSqrt.lt x.extent y.extent)

/-- Sorts rows by extent, then by length. -/
def byExtent (rs : Array Row) : Array Row :=
  rs.qsort fun x y => QSqrt.lt x.extent y.extent ||
    (x.extent == y.extent && x.w.length < y.w.length)

/-- Whether the word has five equal letters in a row that all act: a full turn of one centre of
the moving frame about the other. -/
def fullTurn (w : List Letter) : Bool :=
  let acts := (statesFor r2 w).tail.map (·.acted)
  let cells := w.zip acts
  (List.range (w.length + 1 - 5)).any fun i =>
    let block := (cells.drop i).take 5
    block.all (·.2) && (block.all (·.1 == .a) || block.all (·.1 == .b))

/-- Prints the reports and the search results. -/
def report : IO Unit := do
  for w in ["abab", "aababaabbabb", "ababbab", "aabaaa", "aabaaabbbbb"] do
    IO.println (wordReport r2 (← IO.ofExcept (parseWord w)))
    IO.println ""
  let st := State.start origin
  let (h0, c0) := reach st
  let rows : Array Row := search maxLen st [] [] 0 0 h0 c0 #[]
  IO.println s!"{rows.size} words of 1 to {maxLen} letters"
  let closed := rows.filter fun (r : Row) => r.closed && !r.idle.isEmpty
  let counts := (List.range (maxLen + 1)).filterMap fun n =>
    let k := (closed.filter (fun (r : Row) => r.w.length == n)).size
    if k == 0 then none else some (n, k)
  IO.println s!"closed words with an idle letter, by length: {counts}"
  let shortest := closed.foldl (fun m (r : Row) => min m r.w.length) (maxLen + 1)
  IO.println s!"-- the shortest closed words with an idle letter ({shortest} letters):"
  for r in byExtent (closed.filter (fun (r : Row) => r.w.length == shortest)) do
    IO.println r.text
  let both := closed.filter fun (r : Row) => r.actsA > 0 && r.actsB > 0
  let counts := (List.range (maxLen + 1)).filterMap fun n =>
    let k := (both.filter (fun (r : Row) => r.w.length == n)).size
    if k == 0 then none else some (n, k)
  IO.println s!"closed words with an idle letter in which a and b both act, by length: {counts}"
  let shortest := both.foldl (fun m (r : Row) => min m r.w.length) (maxLen + 1)
  IO.println s!"-- the shortest of them ({shortest} letters), smallest extent first:"
  for r in byExtent (both.filter (fun (r : Row) => r.w.length == shortest)) do
    IO.println r.text
  IO.println "-- the closed ones of smallest extent, shortest first:"
  for r in (byExtent both).extract 0 12 do
    IO.println r.text
  let mixed := both.filter fun (r : Row) => !fullTurn r.w
  IO.println (s!"-- the closed ones in which no letter acts five times in a row ({mixed.size}), " ++
    "shortest first:")
  for r in (byLength mixed).extract 0 12 do
    IO.println r.text
  let one := rows.filter fun (r : Row) => 6 ≤ r.w.length && r.w.length ≤ 8 && r.idle.length == 1 &&
    r.idle != [1] && r.idle != [r.w.length] && r.actsA > 0 && r.actsB > 0
  IO.println (s!"-- words of 6 to 8 letters with one idle letter inside ({one.size}), " ++
    "smallest extent first:")
  for r in (byExtent one).extract 0 20 do
    IO.println r.text

#eval report
