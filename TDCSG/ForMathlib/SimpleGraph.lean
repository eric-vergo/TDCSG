/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, OpenAI GPT-6.2 Astra, Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Walks that cross a cut only through leaves

Let `S` be a set of vertices of a simple graph that contains a vertex `s` and all its neighbours.
If every edge between `S` and its complement has an endpoint whose only neighbour is the other
endpoint, then walks from `s` leave `S` by at most one step.

## Main statements

* `SimpleGraph.Reachable.mem_or_exists_adj_of_leaf`: every vertex reachable from `s` lies in
  `S` or is adjacent to a vertex of `S`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Let `S` contain `s` and all its neighbours, and suppose that every edge from `a ∈ S` to
`b ∉ S` has a leaf endpoint: `b` is the only neighbour of `a`, or `a` is the only neighbour of
`b`. Then every vertex reachable from `s` lies in `S` or is adjacent to a vertex of `S`. -/
theorem Reachable.mem_or_exists_adj_of_leaf {S : Set V} {s v : V} (hs : s ∈ S)
    (hstart : G.neighborSet s ⊆ S)
    (hcross : ∀ a b, a ∈ S → b ∉ S → G.Adj a b → G.neighborSet a ⊆ {b} ∨ G.neighborSet b ⊆ {a})
    (h : G.Reachable s v) : v ∈ S ∨ ∃ w ∈ S, G.Adj w v := by
  rw [reachable_iff_reflTransGen] at h
  -- A vertex of `S` is anchored if it is `s` or has a neighbour in `S`.
  let Anchored (a : V) : Prop := a ∈ S ∧ (a = s ∨ ∃ b ∈ S, G.Adj b a)
  suffices H : Anchored v ∨ ∃ a, Anchored a ∧ G.Adj a v ∧ ∀ w, G.Adj v w → w = a by
    rcases H with H | ⟨a, ha, he, -⟩
    · exact .inl H.1
    · exact .inr ⟨a, ha.1, he⟩
  induction h with
  | refl => exact .inl ⟨hs, .inl rfl⟩
  | @tail a b _ he ih =>
    rcases ih with ha | ⟨u, hu, -, hleaf⟩
    · by_cases hb : b ∈ S
      · exact .inl ⟨hb, .inr ⟨a, ha.1, he⟩⟩
      · rcases hcross a b ha.1 hb he with hl | hl
        · exfalso
          rcases ha.2 with rfl | ⟨w, hw, hwa⟩
          · exact hb (hstart he)
          · exact hb (Set.mem_singleton_iff.1 (hl hwa.symm) ▸ hw)
        · exact .inr ⟨a, ha, he, hl⟩
    · exact .inl (hleaf _ he ▸ hu)

end SimpleGraph
