import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# The side bounds of an extremal-region witness

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` has sides no longer than `ε` and its arc `t_2` between `lo` and `hi`.
Lane gl-p10-11b.

* `sideBound` (proved): `P10ExtremalSplit.RoseExtremalSideBoundStatement`.
  *Proof.*  Clause 4 of `ExtremalContigClauses` says `s₁ ++ t₁⁻¹ ++ s₂ ++ t₂` is a permutation of
  a filter of the nodup boundary cycle `K.boundary.cycle`, so it is nodup, and so are its first
  and third blocks `s₁`, `s₂`.  Clause 15 puts each of `s₁`, `s₂` inside one of the old sides; a
  nodup list contained in a list is a subpermutation of it (`List.subperm_of_subset`), so its
  length is at most the side length, which is at most `ε` (`K.firstSide_length_le`,
  `K.secondSide_length_le`).  Clauses 13 and 14 put `t₂` inside the old target arc by positions,
  and `K.lo_le`, `K.le_hi` bound that arc by `lo` and `hi`.
* `extremalCore_of_contiguity` (proved): the contiguity statement alone gives
  `P10RegionMove.RoseExtremalCoreStatement`.
* `Piece10.proof_of_contiguity` (proved): the contiguity statement alone gives
  `PocketOuterPinchStepSectionStatement`.

## Truth check

The side-bound statement is true: the argument above uses only clauses 4, 13, 14, 15 and the
fields of `PocketFaceSet`.  The remaining gap is `P10ExtremalSplit.RoseExtremalContiguityStatement`
(lane gl-p10-11a).  Risk carried by that gap, not by this file: a wrapping target arc
(`K.targetArc.start + K.targetArc.length > (outerDarts X).length`) whose extremal region eats a
prefix of the arc across the base point has no `t₂` with `K.targetArc.start ≤ t₂.start`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound

universe u w v

section Lists

variable {α : Type*}

/-- The first block of a nodup four-block list is nodup. -/
theorem nodup_block_first {a b c d : List α} (h : (a ++ b ++ c ++ d).Nodup) : a.Nodup :=
  List.Nodup.sublist ((List.sublist_append_left a b).trans
    ((List.sublist_append_left (a ++ b) c).trans (List.sublist_append_left (a ++ b ++ c) d))) h

/-- The third block of a nodup four-block list is nodup. -/
theorem nodup_block_third {a b c d : List α} (h : (a ++ b ++ c ++ d).Nodup) : c.Nodup :=
  List.Nodup.sublist ((List.sublist_append_right (a ++ b) c).trans
    (List.sublist_append_left (a ++ b ++ c) d)) h

/-- A nodup list whose members lie in `l` is no longer than `l`. -/
theorem length_le_of_forall_mem {s l : List α} (hs : s.Nodup) (h : ∀ x ∈ s, x ∈ l) :
    s.length ≤ l.length :=
  (List.subperm_of_subset hs (by intro x hx; exact h x hx)).length_le

end Lists

/-- **The side-bound statement holds.** -/
theorem sideBound : P10ExtremalSplit.RoseExtremalSideBoundStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ _ _ _ hcl
  obtain ⟨-, -, -, hperm, -, -, -, -, -, -, -, -, hst, hen, hsides⟩ := hcl
  have hnd := hperm.nodup_iff.mpr (K.boundary.cycle_nodup.filter _)
  have hlo := Nat.le_trans K.lo_le hst
  have hhi := Nat.le_trans hen K.le_hi
  rcases hsides with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨(length_le_of_forall_mem (nodup_block_first hnd) h₁).trans K.firstSide_length_le,
      (length_le_of_forall_mem (nodup_block_third hnd) h₂).trans K.secondSide_length_le,
      hlo, hhi⟩
  · exact ⟨(length_le_of_forall_mem (nodup_block_first hnd) h₁).trans K.secondSide_length_le,
      (length_le_of_forall_mem (nodup_block_third hnd) h₂).trans K.firstSide_length_le,
      hlo, hhi⟩

/-- **The extremal-region core from contiguity alone.** -/
theorem extremalCore_of_contiguity
    (h : P10ExtremalSplit.RoseExtremalContiguityStatement.{u, w, v}) :
    P10RegionMove.RoseExtremalCoreStatement.{u, w, v} :=
  P10ExtremalSplit.extremalCore_of_contiguity_sideBound h sideBound

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

/-- **The outer pinch step section from contiguity alone.** -/
theorem proof_of_contiguity (h : P10ExtremalSplit.RoseExtremalContiguityStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_extremalCore (P10ExtremalSideBound.extremalCore_of_contiguity h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound.nodup_block_first
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound.nodup_block_third
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound.length_le_of_forall_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound.sideBound
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalSideBound.extremalCore_of_contiguity
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_contiguity
