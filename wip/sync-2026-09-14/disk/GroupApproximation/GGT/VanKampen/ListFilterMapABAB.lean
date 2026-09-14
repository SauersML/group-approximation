import GroupApproximation.GGT.VanKampen.ListNoABABLength
import GroupApproximation.Meta.AxiomGuard

/-!
# An `a b a b` in a word read through a partial map

Read positions `0, …, n − 1` through a partial map `f : ℕ → Option α`: `(range n).filterMap f`.
A subsequence `a b a b` of the word read comes from four positions `s₁ < s₂ < s₃ < s₄ < n` with
`f s₁ = some a`, `f s₂ = some b`, `f s₃ = some a`, `f s₄ = some b`.

In the contact count of Osin's Lemma 9.4 the positions are the sides of a polygon and `f` reads the
object across a side, so an `a b a b` in the object word gives four sides in walk order along
alternating objects, which `neighbourFacesNoninterleaving` excludes.

* `ListNoABAB.exists_index_of_filterMap_eq_cons`: the position of the first letter.
* `ListNoABAB.exists_abab_positions`: the four positions.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.ListNoABAB

open List

variable {α : Type*}

/-- **The position of the first letter** of a word read through `f`. -/
theorem exists_index_of_filterMap_eq_cons {f : ℕ → Option α} {l : List ℕ} {b : α}
    {bs : List α} (h : l.filterMap f = b :: bs) :
    ∃ l₁ s l₂, l = l₁ ++ s :: l₂ ∧ f s = some b ∧ l₂.filterMap f = bs := by
  obtain ⟨l₁, s, l₂, hl, -, hs, hl₂⟩ := List.filterMap_eq_cons_iff.mp h
  exact ⟨l₁, s, l₂, hl, hs, hl₂⟩

/-- **Four positions of an `a b a b`.** -/
theorem exists_abab_positions {f : ℕ → Option α} {n : ℕ} {a b : α}
    (h : [a, b, a, b] <+ (List.range n).filterMap f) :
    ∃ s₁ s₂ s₃ s₄ : ℕ, s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ < s₄ ∧ s₄ < n ∧
      f s₁ = some a ∧ f s₂ = some b ∧ f s₃ = some a ∧ f s₄ = some b := by
  obtain ⟨l, hl, hw⟩ := List.sublist_filterMap_iff.mp h
  have hpw : l.Pairwise (· < ·) := List.Pairwise.sublist hl List.pairwise_lt_range
  have hmem : ∀ x ∈ l, x < n := fun x hx => List.mem_range.mp (hl.subset hx)
  obtain ⟨u₁, s₁, r₁, hl₁, h₁, hr₁⟩ := exists_index_of_filterMap_eq_cons hw.symm
  obtain ⟨u₂, s₂, r₂, hl₂, h₂, hr₂⟩ := exists_index_of_filterMap_eq_cons hr₁
  obtain ⟨u₃, s₃, r₃, hl₃, h₃, hr₃⟩ := exists_index_of_filterMap_eq_cons hr₂
  obtain ⟨u₄, s₄, r₄, hl₄, h₄, -⟩ := exists_index_of_filterMap_eq_cons hr₃
  subst hl₄
  subst hl₃
  subst hl₂
  subst hl₁
  have hA := List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1
  have hB := List.pairwise_cons.mp (List.pairwise_append.mp hA.2).2.1
  have hC := List.pairwise_cons.mp (List.pairwise_append.mp hB.2).2.1
  refine ⟨s₁, s₂, s₃, s₄, hA.1 s₂ (by simp), hB.1 s₃ (by simp), hC.1 s₄ (by simp),
    hmem s₄ (by simp), h₁, h₂, h₃, h₄⟩

end GroupApproximation.GGT.VanKampen.ListNoABAB

#audit_axioms GroupApproximation.GGT.VanKampen.ListNoABAB.exists_index_of_filterMap_eq_cons
#audit_axioms GroupApproximation.GGT.VanKampen.ListNoABAB.exists_abab_positions
