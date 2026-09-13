import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Logic.Relation
import GroupApproximation.Meta.AxiomGuard

/-!
# Word graphs of a subshift

Let `X ⊆ A^ℤ` be a set of configurations over an alphabet `A`.  Its word graph at level `r` has the
words of length `r` of `X` as vertices and the words of length `r + 1` as edges, from prefix to
suffix.  An edge is cyclic if it lies on a directed cycle, and `X` satisfies the cycle condition if
every edge of every word graph is cyclic (sec:chain-core, proof of lem:chain-core-models).

* `word x i n`: the word of length `n` read from `x` at position `i`;
* `language X n`: the words of length `n` of `X`;
* `wordEdge X r u v`, `wordGraph X r`: the word graph at level `r`;
* `IsCyclicEdge X r w`: a directed path leads from the suffix of the edge `w` back to its prefix;
* `CycleCondition X`: every edge of every word graph of `X` is cyclic.

Shift invariance is spelled `∀ n, Set.MapsTo (shift n) X X`, the `mapsTo` field of a Mathlib
`Subshift`.
-/

namespace GroupApproximation
namespace WordGraph

open SymbolicDynamics.FullShift

variable {A : Type*}

/-- The word of length `n` read from `x` starting at position `i`. -/
def word (x : ℤ → A) (i : ℤ) (n : ℕ) : Fin n → A := fun j => x (i + (j : ℕ))

/-- The words of length `n` of `X`: those read from a point of `X` at position `0`. -/
def language (X : Set (ℤ → A)) (n : ℕ) : Set (Fin n → A) :=
  {w | ∃ x ∈ X, word x 0 n = w}

/-- An edge of the word graph of `X` at level `r` from `u` to `v`: a word of length `r + 1` of `X`
with prefix `u` and suffix `v`. -/
def wordEdge (X : Set (ℤ → A)) (r : ℕ) (u v : Fin r → A) : Prop :=
  ∃ w ∈ language X (r + 1), Fin.init w = u ∧ Fin.tail w = v

/-- The word graph of `X` at level `r`: the words of length `r` of `X`, joined from prefix to
suffix by the words of length `r + 1`. -/
def wordGraph (X : Set (ℤ → A)) (r : ℕ) : Digraph (language X r) where
  Adj u v := wordEdge X r u.1 v.1

/-- An edge `w` of the word graph at level `r` is **cyclic** if it lies on a directed cycle, that
is, a directed path leads from its suffix back to its prefix. -/
def IsCyclicEdge (X : Set (ℤ → A)) (r : ℕ) (w : Fin (r + 1) → A) : Prop :=
  w ∈ language X (r + 1) ∧ Relation.ReflTransGen (wordEdge X r) (Fin.tail w) (Fin.init w)

/-- The **cycle condition**: every edge of every word graph of `X` is cyclic. -/
def CycleCondition (X : Set (ℤ → A)) : Prop :=
  ∀ (r : ℕ) (w : Fin (r + 1) → A), w ∈ language X (r + 1) → IsCyclicEdge X r w

@[simp]
theorem word_apply (x : ℤ → A) (i : ℤ) (n : ℕ) (j : Fin n) : word x i n j = x (i + (j : ℕ)) :=
  rfl

theorem word_shift (x : ℤ → A) (k i : ℤ) (n : ℕ) : word (shift k x) i n = word x (k + i) n := by
  funext j
  simp only [word_apply, shift_apply, add_assoc]

theorem init_word (x : ℤ → A) (i : ℤ) (n : ℕ) : Fin.init (word x i (n + 1)) = word x i n := by
  funext j
  simp only [Fin.init, word_apply, Fin.val_castSucc]

theorem tail_word (x : ℤ → A) (i : ℤ) (n : ℕ) :
    Fin.tail (word x i (n + 1)) = word x (i + 1) n := by
  funext j
  simp only [Fin.tail, word_apply, Fin.val_succ]
  congr 1
  omega

/-- The words read from a point of a shift-invariant `X` belong to its language. -/
theorem word_mem_language {X : Set (ℤ → A)} (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X)
    {x : ℤ → A} (hx : x ∈ X) (i : ℤ) (n : ℕ) : word x i n ∈ language X n :=
  ⟨shift i x, hX i hx, by rw [word_shift, add_zero]⟩

/-- The prefix of a word of `X` is a word of `X`. -/
theorem init_mem_language {X : Set (ℤ → A)} {n : ℕ} {w : Fin (n + 1) → A}
    (hw : w ∈ language X (n + 1)) : Fin.init w ∈ language X n := by
  obtain ⟨x, hx, rfl⟩ := hw
  exact ⟨x, hx, (init_word x 0 n).symm⟩

/-- The suffix of a word of a shift-invariant `X` is a word of `X`. -/
theorem tail_mem_language {X : Set (ℤ → A)} (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) {n : ℕ}
    {w : Fin (n + 1) → A} (hw : w ∈ language X (n + 1)) : Fin.tail w ∈ language X n := by
  obtain ⟨x, hx, rfl⟩ := hw
  rw [tail_word]
  exact word_mem_language hX hx _ _

/-- Consecutive words of length `r` read from a point of `X` are joined by an edge. -/
theorem wordEdge_word {X : Set (ℤ → A)} (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) {x : ℤ → A}
    (hx : x ∈ X) (i : ℤ) (r : ℕ) : wordEdge X r (word x i r) (word x (i + 1) r) :=
  ⟨word x i (r + 1), word_mem_language hX hx i (r + 1), init_word x i r, tail_word x i r⟩

/-- A word of `X` read from `s` at position `i` is read from a point of `X` at the same
position. -/
theorem exists_realize_of_word_mem_language {X : Set (ℤ → A)}
    (hX : ∀ n : ℤ, Set.MapsTo (shift n) X X) {s : ℤ → A} {i : ℤ} {n : ℕ}
    (hs : word s i n ∈ language X n) : ∃ y ∈ X, ∀ j : ℕ, j < n → y (i + j) = s (i + j) := by
  obtain ⟨x, hx, hxs⟩ := hs
  refine ⟨shift (-i) x, hX (-i) hx, fun j hj => ?_⟩
  have h := congrFun hxs ⟨j, hj⟩
  simp only [word_apply, zero_add] at h
  rw [shift_apply, neg_add_cancel_left]
  exact h

/-- At level `0` the only vertex is the empty word, so every edge is a loop and is cyclic. -/
theorem isCyclicEdge_zero {X : Set (ℤ → A)} {w : Fin 1 → A} (hw : w ∈ language X 1) :
    IsCyclicEdge X 0 w := by
  refine ⟨hw, ?_⟩
  have h : Fin.tail w = Fin.init w := Subsingleton.elim _ _
  simp only [h, Relation.ReflTransGen.refl]

end WordGraph
end GroupApproximation

#audit_axioms GroupApproximation.WordGraph.word_shift
#audit_axioms GroupApproximation.WordGraph.tail_mem_language
#audit_axioms GroupApproximation.WordGraph.wordEdge_word
#audit_axioms GroupApproximation.WordGraph.exists_realize_of_word_mem_language
#audit_axioms GroupApproximation.WordGraph.isCyclicEdge_zero
