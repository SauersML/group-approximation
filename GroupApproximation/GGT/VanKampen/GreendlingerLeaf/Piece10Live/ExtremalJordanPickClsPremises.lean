import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickClsDiagram
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleavingModels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The premises of `ExtremalJordanStatement` on the counterexample pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-40.

The pocket `ExtremalJordanPickClsModel.pK` meets every hypothesis of `ExtremalJordanStatement`.
* `hwrap`: `4 ≤ 4`, the exterior boundary `[8,10,12,14]`.
* `closedWalk`: the boundary cycle `[0,2,4,6,8,10,12]` is a closed walk.
* `notFirstTurns`: the turn `0 → 2` rotates from `2` past `14` and the walk dart `13` before `1`.
* `srcLt`, `tgtLt`: both arcs have three of five and three of four darts.
* `notUnpinched`: the boundary darts `0` and `2` share a vertex.
* `allCrossed`: the non-first turns are at `0`, `6` and `12`.  The first is crossed by the passage
  of `6`, and the other two by the passage of `0`.  The other turns are one rotation step.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

open NoncrossingClosedWalkEulerNoninterleavingModels (not_rotationBetween_of_first)

/-- The successor of each dart of the boundary cycle (`0` off the cycle). -/
def nxt : Fin 16 → Fin 16 := ![2, 0, 4, 0, 6, 0, 8, 0, 10, 0, 12, 0, 0, 0, 0, 0]

theorem sameCycle_of (d e : Fin 16) (h : vClass d = vClass e) :
    diagram.toCombMap.sigma.SameCycle d e :=
  (CombMap.vertexOf_eq_iff diagram.toCombMap d e).mp ((vClass_iff d e).mpr h)

theorem hwrap : 4 ≤ (Embedded.outerDarts diagram).length :=
  (congrArg List.length outerDarts_eq).symm.le

theorem srcLt : pK.sourceArc.length < (Embedded.cellDarts diagram pK.source).length :=
  (by decide : (3 : ℕ) < 5).trans_eq (congrArg List.length cellDarts_iS).symm

theorem tgtLt : pK.targetArc.length < (Embedded.outerDarts diagram).length :=
  (by decide : (3 : ℕ) < 4).trans_eq (congrArg List.length outerDarts_eq).symm

theorem closedWalk : pK.ClosedWalk := by
  have h : List.IsChain (fun d e : Fin 16 => vClass (M.alpha d) = vClass e) cyc := by decide
  refine ⟨h.imp (by intro a b hab; exact (vClass_iff _ _).mpr hab), (vClass_iff _ _).mpr ?_⟩
  decide

theorem notFirstTurns : ¬pK.FirstTurns := by
  intro hft
  obtain ⟨k, hk, hkv, ht⟩ := (List.isChain_cons_cons.mp
    (show List.IsChain _ ((0 : diagram.toCombMap.Dart) :: 2 :: [4, 6, 8, 10, 12]) from hft.1)).1
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · interval_cases k <;> exact absurd hkv (by decide)
  · exact ht 2 (by decide) (by omega) (Or.inl (by decide))

theorem notUnpinched : ¬Surgery.MapCollapse.Unpinched diagram.toCombMap pK.faces := fun h =>
  absurd (h 0 2 ((bd_iff 0).mpr (by decide)) ((bd_iff 2).mpr (by decide))
    ((vClass_iff 0 2).mpr (by decide))) (by decide)

theorem mem_cyc : ∀ d : diagram.toCombMap.Dart, d ∈ pK.boundary.cycle →
    d = 0 ∨ d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8 ∨ d = 10 ∨ d = 12 := by
  decide

theorem next_eq (inst : DecidableEq diagram.toCombMap.Dart) :
    ∀ d hd, @List.next _ inst pK.boundary.cycle d hd = nxt d := by
  obtain rfl : inst = instDecEqDiagramDart := Subsingleton.elim _ _
  decide

/-- **Every non-first turn of the pocket is crossed.** -/
theorem allCrossed : GreendlingerLeaf.P10ChordLift.AllNonFirstTurnsCrossed pK := by
  intro d₀ hd₀ hnf
  unfold GreendlingerLeaf.P10ChordLift.NonFirstTurn at hnf
  unfold GreendlingerLeaf.P10ChordLift.TurnCrossed
  rcases mem_cyc d₀ hd₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨6, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨2, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · rw [next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨0, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mpr ⟨1, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · rw [next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨0, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨3, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)

end GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel

#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.nxt
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.sameCycle_of
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.hwrap
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.srcLt
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.tgtLt
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.notFirstTurns
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.notUnpinched
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.mem_cyc
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.next_eq
#audit_axioms GroupApproximation.GGT.VanKampen.ExtremalJordanPickClsModel.allCrossed
