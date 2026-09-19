import Mathlib.Data.List.Infix
import GroupApproximation.Meta.AxiomGuard

/-!
# Filtering a list whose kept entries form one block

If a list splits as `r₁ ++ k ++ r₂`, where the predicate is `false` on `r₁` and `r₂` and `true` on
`k`, then filtering it gives `k`.  So the filtered list is an infix of the list.  If the removed
entries are a suffix, the filtered list is a prefix.

These are the list halves of clauses (b) and (c) of the quadrant move
(`GreendlingerLeaf.P10FilterMoveExists.p10FM_QuadrantMoveStatement`):
* (b) `(a.darts.reverse.map M.alpha).filter keep <:+: a.darts.reverse.map M.alpha`;
* (c) `b.darts.filter keep <+: b.darts`.

Each clause follows once the kept darts of the arc form one block, or a prefix for `b`.  Which
choice of the removed stretch `B` gives those blocks is the geometric part of the move, item 5 on
the nm-gl03d board; it is not proved here.

* `filter_eq_of_kept_block`, `filter_infix_of_kept_block`, `filter_prefix_of_kept_prefix`.
* `arcClauses_of_blocks`: clauses (b) and (c) together, from the two block decompositions.

Lane nm-osin94, for nm-gl03d.

## Manuscript status

Infrastructure for `thm:hull` (residual 10 of the Below waist).  It certifies no printed sentence
on its own.
-/

namespace GroupApproximation.GGT.VanKampen.ListFilterBlocks

variable {α : Type*} {p : α → Bool}

/-- **Filtering a list whose kept entries are one block** gives that block. -/
theorem filter_eq_of_kept_block {r₁ k r₂ : List α} (h₁ : ∀ x ∈ r₁, p x = false)
    (hk : ∀ x ∈ k, p x = true) (h₂ : ∀ x ∈ r₂, p x = false) :
    (r₁ ++ k ++ r₂).filter p = k := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [h₁ x hx]),
    List.filter_eq_self.mpr hk,
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [h₂ x hx])]
  simp

/-- **Clause (b) from one kept block**: the filtered list is an infix. -/
theorem filter_infix_of_kept_block {r₁ k r₂ : List α} (h₁ : ∀ x ∈ r₁, p x = false)
    (hk : ∀ x ∈ k, p x = true) (h₂ : ∀ x ∈ r₂, p x = false) :
    (r₁ ++ k ++ r₂).filter p <:+: r₁ ++ k ++ r₂ := by
  rw [filter_eq_of_kept_block h₁ hk h₂]
  exact List.infix_append r₁ k r₂

/-- **Clause (c) from a kept prefix**: if the removed entries are a suffix, the filtered list is a
prefix. -/
theorem filter_prefix_of_kept_prefix {k r : List α} (hk : ∀ x ∈ k, p x = true)
    (hr : ∀ x ∈ r, p x = false) :
    (k ++ r).filter p <+: k ++ r := by
  have h := filter_eq_of_kept_block (p := p) (r₁ := []) (k := k) (r₂ := r) (by simp) hk hr
  simp only [List.nil_append] at h
  rw [h]
  exact List.prefix_append k r

/-- **Clauses (b) and (c) of the quadrant move from the block decompositions.**  If the kept entries
of `A` form one block and the kept entries of `B` form a prefix, then `A.filter p <:+: A` and
`B.filter p <+: B`. -/
theorem arcClauses_of_blocks {A B : List α}
    (hA : ∃ r₁ k r₂ : List α, A = r₁ ++ k ++ r₂ ∧ (∀ x ∈ r₁, p x = false) ∧
      (∀ x ∈ k, p x = true) ∧ (∀ x ∈ r₂, p x = false))
    (hB : ∃ k r : List α, B = k ++ r ∧ (∀ x ∈ k, p x = true) ∧ (∀ x ∈ r, p x = false)) :
    A.filter p <:+: A ∧ B.filter p <+: B := by
  obtain ⟨r₁, k, r₂, rfl, h₁, hk, h₂⟩ := hA
  obtain ⟨k', r, rfl, hk', hr⟩ := hB
  exact ⟨filter_infix_of_kept_block h₁ hk h₂, filter_prefix_of_kept_prefix hk' hr⟩

end GroupApproximation.GGT.VanKampen.ListFilterBlocks

#audit_axioms GroupApproximation.GGT.VanKampen.ListFilterBlocks.filter_eq_of_kept_block
#audit_axioms GroupApproximation.GGT.VanKampen.ListFilterBlocks.filter_infix_of_kept_block
#audit_axioms GroupApproximation.GGT.VanKampen.ListFilterBlocks.filter_prefix_of_kept_prefix
#audit_axioms GroupApproximation.GGT.VanKampen.ListFilterBlocks.arcClauses_of_blocks
