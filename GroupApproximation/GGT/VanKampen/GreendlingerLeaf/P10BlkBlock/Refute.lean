import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.Tables
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.BlkBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# `roseLobeBlk_BlockStatement` is FALSE

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

**LOUD: `P10RoseLobe.roseLobeBlk_BlockStatement` is FALSE** (`not_blockStatement`),
and so is the equivalent `P10RoseLobe.roseLobeFL_BlockStatement`
(`not_flBlockStatement`, through `roseLobeBlk_weak_of_block`).  Do not try to prove
either one.

## The counterexample

The map `P10BlkBlockModel.M` has sixteen darts, three vertices and seven faces
(`P10BlkBlock.Map`).  The disc diagram `P10BlkBlockModel.diagram` has the outer face
`1 = [1,14]` and the relator cells `K₀ = [0,15,4]` and `S = [3]` (`P10BlkBlock.Diagram`).  The
pocket `P10BlkBlockModel.pK` has the faces `0 = [0,15,4]`, `2 = [2,6,10,11]` and `6 = [8,13]`.
Its source cell is `S` and its kept cell is `K₀`, and its boundary walk is
`cyc = [0,15,2,8,6,4,13]`.  It meets every hypothesis of the statement (`P10BlkBlock.Premises`).

The walk classes are the seven faces (`P10BlkBlock.Classes`).  Now take any list of roots `rs`.
* The kept cell must flip, so no root lies on the face `0`.  The source cell must not flip, so
  no root lies on the face `3`.
* If `rs` lies on the walk, the marked faces are a nonempty subset of `{2, 6}` (table `tabA`).
* If `rs = [r]` is a single root away from the exterior, then `r` is not on the face `1`, so it
  marks exactly one face `c ≠ 1, 3` (table `tabB`).
* For each of these tables, no split `cyc = A ++ B ++ C` is a removed or kept block
  (`P10BlkBlock.Tables`, checked by `decide +kernel`).

## Truth check

The failure was found and rechecked by exhaustive search over all root lists and all splits
(scratch `gl-p10-88/blk_audit.py`, `hyp_check.py`, `blk_generic.py`).  It is the first failing
configuration of the gl-p10-72 search.

## Manuscript status

A refutation of a formal intermediate statement for `thm:hull`.  It certifies no printed
sentence.  The manuscript's lobe step needs a different removed set than one lobe colouring
with a single contiguous block.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

open SimpleClosedWalkSides (walkKeep)
open GreendlingerLeaf.P10RoseExtremalTrim (roseJunctionCore_lobeColour)
open GreendlingerLeaf.P10Rose.FilterMove (movePred)

/-- The moved darts of the lobe move of `rs`, read off the table of its marked faces. -/
theorem move_eq (rs : List diagram.toCombMap.Dart) (T : Fin 7 → Bool)
    (hT : ∀ k, decide (∃ r ∈ rs, faceClass r = k) = T k) :
    movePred diagram.toCombMap (roseJunctionCore_lobeColour diagram.toCombMap
      (walkKeep diagram.toCombMap pK.boundary.cycle) rs) = mvT T := by
  funext x
  unfold movePred mvT
  rw [colour_eq, colour_eq, hT, hT, faceClass_alpha]

theorem tabA_other :
    ∀ (b2 b6 : Bool) (k : Fin 7), k ≠ 2 → k ≠ 6 → tabA b2 b6 k = false := by
  decide

/-- **The counterexample.** -/
theorem refute : ¬GreendlingerLeaf.P10RoseLobe.roseLobeBlk_BlockStatement.{0, 0, 0} := by
  intro h
  obtain ⟨rs, hroot, hsrc, hkept, -, -, A, B, C, hABC, hblk⟩ :=
    h OsinPocketPinchedTwoGonModel.D 7 diagram 0 0 leastArea letters pK closedWalk notFirstTurns
      srcLt tgtLt notUnpinched allCrossed
  have h0 := (keptFlip rs).mp hkept
  rcases hroot with ⟨hne, hrs⟩ | ⟨r, rfl, hout, -⟩
  · have hT : ∀ k, decide (∃ r ∈ rs, faceClass r = k) =
        tabA (decide (∃ r ∈ rs, faceClass r = 2))
          (decide (∃ r ∈ rs, faceClass r = 6)) k := by
      intro k
      by_cases h2 : k = 2
      · subst h2
        rfl
      by_cases h6 : k = 6
      · subst h6
        rfl
      rw [tabA_other _ _ k h2 h6]
      by_cases hk0 : k = 0
      · subst hk0
        exact h0
      refine decide_eq_false ?_
      rintro ⟨r, hr, e⟩
      rcases cyc_class r (hrs r hr) with e' | e' | e'
      · exact hk0 (e.symm.trans e')
      · exact h2 (e.symm.trans e')
      · exact h6 (e.symm.trans e')
    have hor : (decide (∃ r ∈ rs, faceClass r = 2) || decide (∃ r ∈ rs, faceClass r = 6)) =
        true := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil rs hne
      rcases cyc_class r (hrs r hr) with e | e | e
      · have e0 : ∃ r ∈ rs, faceClass r = 0 := ⟨r, hr, e⟩
        exact absurd (h0.symm.trans (decide_eq_true e0)) (by decide)
      · have e2 : ∃ r ∈ rs, faceClass r = 2 := ⟨r, hr, e⟩
        rw [decide_eq_true e2, Bool.true_or]
      · have e6 : ∃ r ∈ rs, faceClass r = 6 := ⟨r, hr, e⟩
        rw [decide_eq_true e6, Bool.or_true]
    rw [move_eq rs _ hT] at hblk
    exact noBlock_of_split (tabA _ _) (noBlockA _ _ hor) hABC hblk
  · have h3 : faceClass r ≠ 3 := by
      intro e
      have e3 : ∃ r' ∈ [r], faceClass r' = 3 := ⟨r, List.mem_singleton_self r, e⟩
      exact hsrc ((srcFlip [r]).mpr (decide_eq_true e3))
    have h1 : faceClass r ≠ 1 := by
      intro e
      refine hout 1 ((faceOf_eq_face 1 1).mpr (by decide)) ((eqvGen_iff r 1).mpr ?_)
      exact e.trans (by decide)
    have hT : ∀ k, decide (∃ r' ∈ [r], faceClass r' = k) = tabB (faceClass r) k := by
      intro k
      unfold tabB
      refine decide_eq_decide.mpr ⟨?_, fun e => ⟨r, List.mem_singleton_self r, e⟩⟩
      rintro ⟨r', hr', e⟩
      rw [List.mem_singleton.mp hr'] at e
      exact e
    rw [move_eq [r] (tabB (faceClass r)) hT] at hblk
    exact noBlock_of_split (tabB (faceClass r)) (noBlockB _ h1 h3) hABC hblk

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.move_eq
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tabA_other
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.refute

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock

/-- **LOUD: `roseLobeBlk_BlockStatement` is FALSE.** -/
theorem not_blockStatement : ¬P10RoseLobe.roseLobeBlk_BlockStatement.{0, 0, 0} :=
  P10BlkBlockModel.refute

/-- **LOUD: `roseLobeFL_BlockStatement` is FALSE**, as it implies `roseLobeBlk_BlockStatement`. -/
theorem not_flBlockStatement : ¬P10RoseLobe.roseLobeFL_BlockStatement.{0, 0, 0} :=
  fun h => not_blockStatement (P10RoseLobe.roseLobeBlk_weak_of_block h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.not_blockStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.not_flBlockStatement
