import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-22: sublists of a four-block word

List combinatorics for `FourBlock.pocketLabelFourBlock_of_curveSublist`
(`FourBlockEndpoint.lean`).  Infrastructure for Osin, arXiv:math/0411039v3, §9, proof of Lemma
9.7(b).  Certifies no printed sentence on its own.

* `exists_blocks_of_sublist`: a sublist of `Q₁ ++ Q₂ ++ Q₃ ++ Q₄` splits as `U₁ ++ U₂ ++ U₃ ++ U₄`
  with every entry of `Uₖ` in `Qₖ`.  This is `List.sublist_append_iff`, applied three times.
* `exists_rotate_blocks_of_reverse_sublist`: if the reverse of `l` is such a sublist, then some
  rotation of `l` splits as `U₁ ++ U₂ ++ U₃ ++ U₄` with entries in `Q₁`, `Q₄`, `Q₃`, `Q₂`.  Reverse
  the split, then rotate the reversed first block to the front (`List.rotate_append_length_eq`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock

variable {α : Type*}

/-- **A sublist of a four-block word reads four blocks.** -/
theorem exists_blocks_of_sublist {l Q₁ Q₂ Q₃ Q₄ : List α} (h : l <+ Q₁ ++ Q₂ ++ Q₃ ++ Q₄) :
    ∃ U₁ U₂ U₃ U₄ : List α, l = U₁ ++ U₂ ++ U₃ ++ U₄ ∧ (∀ e ∈ U₁, e ∈ Q₁) ∧
      (∀ e ∈ U₂, e ∈ Q₂) ∧ (∀ e ∈ U₃, e ∈ Q₃) ∧ ∀ e ∈ U₄, e ∈ Q₄ := by
  obtain ⟨V, U₄, rfl, hV, h₄⟩ := List.sublist_append_iff.mp h
  obtain ⟨V', U₃, rfl, hV', h₃⟩ := List.sublist_append_iff.mp hV
  obtain ⟨U₁, U₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hV'
  exact ⟨U₁, U₂, U₃, U₄, rfl, fun e he => h₁.subset he, fun e he => h₂.subset he,
    fun e he => h₃.subset he, fun e he => h₄.subset he⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.exists_blocks_of_sublist

/-- **A list whose reverse is a sublist of a four-block word reads four blocks after a rotation**,
in the opposite cyclic order of the blocks. -/
theorem exists_rotate_blocks_of_reverse_sublist {l Q₁ Q₂ Q₃ Q₄ : List α}
    (h : l.reverse <+ Q₁ ++ Q₂ ++ Q₃ ++ Q₄) :
    ∃ (k : ℕ) (U₁ U₂ U₃ U₄ : List α), l.rotate k = U₁ ++ U₂ ++ U₃ ++ U₄ ∧
      (∀ e ∈ U₁, e ∈ Q₁) ∧ (∀ e ∈ U₂, e ∈ Q₄) ∧ (∀ e ∈ U₃, e ∈ Q₃) ∧ ∀ e ∈ U₄, e ∈ Q₂ := by
  obtain ⟨V₁, V₂, V₃, V₄, hl, h₁, h₂, h₃, h₄⟩ := exists_blocks_of_sublist h
  have hl' : l = V₄.reverse ++ V₃.reverse ++ V₂.reverse ++ V₁.reverse := by
    have hr := congrArg List.reverse hl
    rw [List.reverse_reverse] at hr
    rw [hr]
    simp only [List.reverse_append, List.append_assoc]
  refine ⟨(V₄.reverse ++ V₃.reverse ++ V₂.reverse).length, V₁.reverse, V₄.reverse, V₃.reverse,
    V₂.reverse, ?_, fun e he => h₁ e (List.mem_reverse.mp he),
    fun e he => h₄ e (List.mem_reverse.mp he), fun e he => h₃ e (List.mem_reverse.mp he),
    fun e he => h₂ e (List.mem_reverse.mp he)⟩
  rw [hl', List.rotate_append_length_eq]
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock.exists_rotate_blocks_of_reverse_sublist

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourBlock
