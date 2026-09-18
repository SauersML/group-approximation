import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.Diagram
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleavingModels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The premises of `roseLobeBlk_BlockStatement` on the counterexample pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

The pocket `P10BlkBlockModel.pK` meets every hypothesis of `roseLobeBlk_BlockStatement`.
* `closedWalk`: the boundary cycle `[0,15,2,8,6,4,13]` is a closed walk.
* `notFirstTurns`: the turn `15 → 2` rotates from `2` to the walk dart `3` before `14`.
* `srcLt`, `tgtLt`: both arcs are empty, of one and two darts.
* `notUnpinched`: the boundary darts `0` and `2` share a vertex.
* `allCrossed`: the turn at `0` is one rotation step.  Each of the other six turns is crossed:
  at `15`, `2` and `6` by the passage of `8`; at `8` and `4` by that of `15`; at `13` by that
  of `2`.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

open NoncrossingClosedWalkEulerNoninterleavingModels (not_rotationBetween_of_first)

/-- The successor of each dart of the boundary cycle (`0` off the cycle). -/
def nxt : Fin 16 → Fin 16 := ![15, 0, 8, 0, 13, 0, 4, 0, 6, 0, 0, 0, 0, 0, 0, 2]

theorem sameCycle_of (d e : Fin 16) (h : vClass d = vClass e) :
    diagram.toCombMap.sigma.SameCycle d e :=
  (CombMap.vertexOf_eq_iff diagram.toCombMap d e).mp ((vClass_iff d e).mpr h)

theorem srcLt : pK.sourceArc.length < (Embedded.cellDarts diagram pK.source).length :=
  (by decide : (0 : ℕ) < 1).trans_eq (congrArg List.length cellDarts_iS).symm

theorem tgtLt : pK.targetArc.length < (Embedded.outerDarts diagram).length :=
  (by decide : (0 : ℕ) < 2).trans_eq (congrArg List.length outerDarts_eq).symm

theorem closedWalk : pK.ClosedWalk := by
  have h : List.IsChain (fun d e : Fin 16 => vClass (M.alpha d) = vClass e) cyc := by decide
  refine ⟨h.imp (by intro a b hab; exact (vClass_iff _ _).mpr hab), (vClass_iff _ _).mpr ?_⟩
  decide

theorem notFirstTurns : ¬pK.FirstTurns := by
  intro hft
  obtain ⟨k, hk, hkv, ht⟩ := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp
    (show List.IsChain _ ((0 : diagram.toCombMap.Dart) :: 15 :: 2 :: [8, 6, 4, 13])
      from hft.1)).2).1
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · interval_cases k <;> exact absurd hkv (by decide)
  · exact ht 1 (by decide) (by omega) (Or.inl (by decide))

theorem notUnpinched : ¬Surgery.MapCollapse.Unpinched diagram.toCombMap pK.faces := fun h =>
  absurd (h 0 2 ((bd_iff 0).mpr (by decide)) ((bd_iff 2).mpr (by decide))
    ((vClass_iff 0 2).mpr (by decide))) (by decide)

theorem mem_cyc : ∀ d : diagram.toCombMap.Dart, d ∈ pK.boundary.cycle →
    d = 0 ∨ d = 15 ∨ d = 2 ∨ d = 8 ∨ d = 6 ∨ d = 4 ∨ d = 13 := by
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
  · rw [next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨8, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 6) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨2, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨8, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mpr ⟨1, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨15, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 6) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mpr ⟨4, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨8, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 10) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mpr ⟨4, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨15, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 5) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨2, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · refine ⟨2, by decide, by decide, sameCycle_of _ _ (by decide), ?_⟩
    rw [next_eq, next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mpr ⟨1, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.nxt
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.sameCycle_of
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.srcLt
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tgtLt
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.notFirstTurns
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.notUnpinched
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.mem_cyc
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.next_eq
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.allCrossed
