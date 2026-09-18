import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Pocket
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleavingModels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionUnpinched
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The premises of `RoseExtremalJunctionStatement` on the 24-dart pocket

Lane gl-p10-51.

The pocket `roseJunctionRefute_pK` meets every hypothesis of
`P10RoseExtremalTrim.RoseExtremalJunctionStatement`.
* `closedWalk`: the boundary cycle `[0,2,16,4,6,18,8,20,10,12,22]` is a closed walk.
* `notFirstTurns`: the turn `0 → 2` rotates from `2` past `14` and the walk dart `23` before `1`.
* `srcLt`, `tgtLt`: the arcs have five of seven and five of six darts.
* `notUnpinched`: the boundary darts `0` and `2` share a vertex.
* `allCrossed`: the non-first turns are at `0`, `18` and `22`, all at the vertex of `0`.  They
  are crossed by the passages of `18`, `22` and `0`.  The other turns are one rotation step.

Proof route: `decide` on the listed darts, and
`NoncrossingClosedWalkEulerNoninterleavingModels.not_rotationBetween_of_first` for the crossings.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open NoncrossingClosedWalkEulerNoninterleavingModels (not_rotationBetween_of_first)

/-- The successor of each dart of the boundary cycle (`0` off the cycle). -/
def roseJunctionRefute_nxt : Fin 24 → Fin 24 :=
  ![2, 0, 16, 0, 6, 0, 18, 0, 20, 0, 12, 0, 22, 0, 0, 0, 4, 0, 8, 0, 10, 0, 0, 0]

theorem roseJunctionRefute_sameCycle (d e : Fin 24)
    (h : roseJunctionRefute_vClass d = roseJunctionRefute_vClass e) :
    roseJunctionRefute_X.toCombMap.sigma.SameCycle d e :=
  (CombMap.vertexOf_eq_iff roseJunctionRefute_X.toCombMap d e).mp
    ((roseJunctionRefute_vClass_iff d e).mpr h)

theorem roseJunctionRefute_srcLt : roseJunctionRefute_pK.sourceArc.length <
    (Embedded.cellDarts roseJunctionRefute_X roseJunctionRefute_pK.source).length :=
  (by decide : (5 : ℕ) < 7).trans_eq (congrArg List.length roseJunctionRefute_cellDarts).symm

theorem roseJunctionRefute_tgtLt : roseJunctionRefute_pK.targetArc.length <
    (Embedded.outerDarts roseJunctionRefute_X).length :=
  (by decide : (5 : ℕ) < 6).trans_eq (congrArg List.length roseJunctionRefute_outerDarts).symm

theorem roseJunctionRefute_closedWalk : roseJunctionRefute_pK.ClosedWalk := by
  have h : List.IsChain (fun d e : Fin 24 => roseJunctionRefute_vClass
      (roseJunctionRefute_M.alpha d) = roseJunctionRefute_vClass e) roseJunctionRefute_cyc := by
    decide
  refine ⟨h.imp (by intro a b hab; exact (roseJunctionRefute_vClass_iff _ _).mpr hab),
    (roseJunctionRefute_vClass_iff _ _).mpr ?_⟩
  decide

theorem roseJunctionRefute_notFirst : ¬roseJunctionRefute_pK.FirstTurns := by
  intro hft
  obtain ⟨k, hk, hkv, ht⟩ := (List.isChain_cons_cons.mp
    (show List.IsChain _ ((0 : roseJunctionRefute_X.toCombMap.Dart) :: 2 ::
      [16, 4, 6, 18, 8, 20, 10, 12, 22]) from hft.1)).1
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · interval_cases k <;> exact absurd hkv (by decide)
  · exact ht 2 (by decide) (by omega) (Or.inl (by decide))

theorem roseJunctionRefute_notUnpinched :
    ¬Surgery.MapCollapse.Unpinched roseJunctionRefute_X.toCombMap roseJunctionRefute_pK.faces :=
  fun h => absurd (h 0 2 ((roseJunctionRefute_bd_iff 0).mpr (by decide))
    ((roseJunctionRefute_bd_iff 2).mpr (by decide))
    ((roseJunctionRefute_vClass_iff 0 2).mpr (by decide))) (by decide)

theorem roseJunctionRefute_mem_cyc : ∀ d : roseJunctionRefute_X.toCombMap.Dart,
    d ∈ roseJunctionRefute_pK.boundary.cycle → d = 0 ∨ d = 2 ∨ d = 16 ∨ d = 4 ∨ d = 6 ∨
      d = 18 ∨ d = 8 ∨ d = 20 ∨ d = 10 ∨ d = 12 ∨ d = 22 := by
  decide

theorem roseJunctionRefute_next_eq (inst : DecidableEq roseJunctionRefute_X.toCombMap.Dart) :
    ∀ d hd, @List.next _ inst roseJunctionRefute_pK.boundary.cycle d hd =
      roseJunctionRefute_nxt d := by
  obtain rfl : inst = roseJunctionRefute_instDecEqX := Subsingleton.elim _ _
  decide

/-- **Every non-first turn of the pocket is crossed.** -/
theorem roseJunctionRefute_allCrossed :
    P10ChordLift.AllNonFirstTurnsCrossed roseJunctionRefute_pK := by
  intro d₀ hd₀ hnf
  unfold P10ChordLift.NonFirstTurn at hnf
  unfold P10ChordLift.TurnCrossed
  rcases roseJunctionRefute_mem_cyc d₀ hd₀ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨18, by decide, by decide, roseJunctionRefute_sameCycle _ _ (by decide), ?_⟩
    rw [roseJunctionRefute_next_eq, roseJunctionRefute_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 3) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨2, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨22, by decide, by decide, roseJunctionRefute_sameCycle _ _ (by decide), ?_⟩
    rw [roseJunctionRefute_next_eq, roseJunctionRefute_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨3, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · rw [roseJunctionRefute_next_eq] at hnf
    exact (hnf (FirstTurn.of_sigma_alpha (by decide))).elim
  · refine ⟨0, by decide, by decide, roseJunctionRefute_sameCycle _ _ (by decide), ?_⟩
    rw [roseJunctionRefute_next_eq, roseJunctionRefute_next_eq]
    exact fun h => not_rotationBetween_of_first (a₀ := 4) (by decide) (by decide)
      (fun b hb0 hb => by interval_cases b <;> decide)
      (h.mp ⟨3, by decide, by decide, fun b hb0 hb => by interval_cases b <;> decide⟩)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
