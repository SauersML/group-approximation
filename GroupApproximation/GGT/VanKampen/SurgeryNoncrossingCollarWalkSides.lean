import GroupApproximation.GGT.VanKampen.SurgeryNoncrossingCollarWalk
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.GGT.VanKampen.PermFirstReturnOrbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Turning back is following the outer boundary

For a noncrossing closed walk `w` in a planar map, the reversed walk is a boundary cycle of the
faces on the other side (`IsNoncrossingClosedWalk.outerCycle`).  This module shows that this cycle
follows its boundary exactly when every walk dart turns back to the walk dart before it
(`outerTurn_iff_followsBoundary`).  So the collar moves of `SurgeryNoncrossingCollarWalk.lean`
keep a noncrossing closed walk whose outer cycle follows its boundary
(`followsBoundary_outerCycle_map`, `followsBoundary_outerCycle_vertexJoin`).

* `outerStep`: a turn back is a boundary walk of the faces on the other side.
* `turnsBack_of_boundaryWalk`: a boundary walk of the other side along the reversed walk is a turn
  back.
* `boundaryWalk_getElem`, `boundaryWalk_getLast_head`: a boundary cycle that follows its boundary
  runs along consecutive entries.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u v

section Boundary

variable {M : CombMap.{u}} {faces : Finset M.Face}

/-- **A boundary walk rotates around one vertex.**  A copy of `BoundaryWalk.exists_pow` of
`FaceSetCircuitNoncrossing.lean` without its imports. -/
theorem boundaryWalk_exists_pow {d e : M.Dart} (h : BoundaryWalk M faces d e) :
    ∃ n : ℕ, (M.sigma ^ (n + 1)) (M.alpha d) = e ∧
      ∀ k, 0 < k → k ≤ n → InternalDart M faces ((M.sigma ^ k) (M.alpha d)) := by
  have h' : Relation.ReflTransGen (fun x y => InternalDart M faces x ∧ M.sigma x = y)
      (M.facePerm d) e := h
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M faces) h'
  have hface : M.facePerm d = M.sigma (M.alpha d) := rfl
  refine ⟨n, ?_, fun k hk hkn => ?_⟩
  · rw [pow_succ, Perm.mul_apply, ← hface]
    exact hn
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply, ← hface]
    exact hskip j (by omega)

/-- A boundary cycle that follows its boundary walks from each entry to the next one. -/
theorem boundaryWalk_getElem {b : BoundaryCycle M faces} (hb : b.FollowsBoundary) (i : ℕ)
    (hi : i + 1 < b.cycle.length) :
    BoundaryWalk M faces (b.cycle[i]'(by omega)) (b.cycle[i + 1]'hi) := by
  have hmem : b.cycle[i]'(by omega) ∈ b.cycle := List.getElem_mem _
  have hd := hb ⟨b.cycle[i]'(by omega), (b.cycle_mem_iff _).mp hmem⟩
  rwa [boundaryPerm_val_of_getElem M faces b i (by omega) _ rfl,
    show finRotate b.cycle.length ⟨i, by omega⟩ = ⟨i + 1, hi⟩ from
      Fin.ext (val_finRotate_of_lt _ hi), List.get_eq_getElem] at hd

/-- A boundary cycle that follows its boundary walks from its last entry to its first one. -/
theorem boundaryWalk_getLast_head {b : BoundaryCycle M faces} (hb : b.FollowsBoundary) :
    BoundaryWalk M faces (b.cycle.getLast b.cycle_nonempty) (b.cycle.head b.cycle_nonempty) := by
  have hlen : 0 < b.cycle.length := List.length_pos_iff.mpr b.cycle_nonempty
  have hmem := List.getLast_mem b.cycle_nonempty
  have hd := hb ⟨b.cycle.getLast b.cycle_nonempty, (b.cycle_mem_iff _).mp hmem⟩
  have hrot : finRotate b.cycle.length ⟨b.cycle.length - 1, by omega⟩ = ⟨0, hlen⟩ :=
    Fin.ext (val_finRotate_of_eq _ (show b.cycle.length - 1 + 1 = b.cycle.length by omega))
  rwa [boundaryPerm_val_of_getElem M faces b (b.cycle.length - 1) (by omega) _
    (List.getLast_eq_getElem b.cycle_nonempty), hrot, List.get_eq_getElem,
    ← List.head_eq_getElem b.cycle_nonempty] at hd

end Boundary

section Sides

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **A turn back is a boundary walk** of the faces on the other side, along the reversed walk. -/
theorem outerStep (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) {a b : M.Dart}
    (hb : b ∈ w) (h : TurnsBack M w a b) :
    BoundaryWalk M (sideOutside M w) (M.alpha b) (M.alpha a) := by
  obtain ⟨m, hm, hpm, havoid⟩ := h
  have hpm' : (M.sigma ^ m) (M.alpha (M.alpha b)) = M.alpha a := by
    rw [M.alpha_involutive b]
    exact hpm
  rw [← hpm']
  refine boundaryWalk_of_run M (walkKeep M w) (sideOutside M w) (M.alpha b) hm ?_ ?_
  · intro k hk0 hkm hkeep
    rw [M.alpha_involutive b] at hkeep
    exact havoid k hk0 hkm hkeep
  · intro x hx
    rw [mem_sideOutside_iff, mem_sideFaces_iff]
    rintro ⟨d, hd, h⟩
    exact hw.not_faceClass_alpha hM hd hb (.trans _ _ _ h (.symm _ _ hx))

/-- **A boundary walk of the other side along the reversed walk is a turn back.** -/
theorem turnsBack_of_boundaryWalk {a b : M.Dart}
    (h : BoundaryWalk M (sideOutside M w) (M.alpha b) (M.alpha a)) : TurnsBack M w a b := by
  obtain ⟨n, hn, hint⟩ := boundaryWalk_exists_pow h
  rw [M.alpha_involutive b] at hn hint
  refine ⟨n + 1, Nat.succ_pos n, hn, fun k hk0 hkn hkeep => ?_⟩
  have hin := (hint k hk0 (by omega)).1
  have hin' := (hint k hk0 (by omega)).2
  rw [mem_sideOutside_iff, mem_sideFaces_iff] at hin hin'
  rcases hkeep with hkeep | hkeep
  · exact hin ⟨_, hkeep, .refl _⟩
  · exact hin' ⟨_, hkeep, .refl _⟩

/-- **The reversed walk follows the boundary** once every walk dart turns back. -/
theorem followsBoundary_outerCycle (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (ht : OuterTurn M w) : (hw.outerCycle hM).FollowsBoundary := by
  refine BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · show (w.reverse.map M.alpha).IsChain (BoundaryWalk M (sideOutside M w))
    rw [List.isChain_map, List.isChain_reverse]
    exact ht.chain.imp_of_mem_imp fun _ _ _ hb h => outerStep hw hM hb h
  · show BoundaryWalk M (sideOutside M w) ((w.reverse.map M.alpha).getLast _)
      ((w.reverse.map M.alpha).head _)
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    exact outerStep hw hM (List.head_mem _) (ht.closes hw.ne_nil)

/-- **Every walk dart turns back** once the reversed walk follows the boundary. -/
theorem outerTurn_of_followsBoundary (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hf : (hw.outerCycle hM).FollowsBoundary) : OuterTurn M w where
  chain := by
    have hchain : (w.reverse.map M.alpha).IsChain (BoundaryWalk M (sideOutside M w)) :=
      List.isChain_iff_getElem.mpr fun i hi => boundaryWalk_getElem hf i hi
    rw [List.isChain_map, List.isChain_reverse] at hchain
    exact hchain.imp_of_mem_imp fun _ _ _ _ h => turnsBack_of_boundaryWalk h
  closes _ := by
    have h : BoundaryWalk M (sideOutside M w)
        ((w.reverse.map M.alpha).getLast (by simpa using hw.ne_nil))
        ((w.reverse.map M.alpha).head (by simpa using hw.ne_nil)) :=
      boundaryWalk_getLast_head hf
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse] at h
    exact turnsBack_of_boundaryWalk h

theorem outerTurn_iff_followsBoundary (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    OuterTurn M w ↔ (hw.outerCycle hM).FollowsBoundary :=
  ⟨followsBoundary_outerCycle hw hM, outerTurn_of_followsBoundary hw hM⟩

end Sides

/-- **A pinch keeps a noncrossing closed walk whose outer cycle follows its boundary.** -/
theorem followsBoundary_outerCycle_vertexJoin {M : CombMap.{u}} [DecidableEq M.Dart]
    {w : List M.Dart} {x y : M.Dart} (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hf : (hw.outerCycle hM).FollowsBoundary) (hx : M.alpha x ∈ w) (hy : M.sigma y ∈ w)
    (hM' : (VertexJoin.toCombMap M x y).IsPlanar) :
    ∃ hw' : IsNoncrossingClosedWalk (VertexJoin.toCombMap M x y) w,
      (hw'.outerCycle hM').FollowsBoundary := by
  have ht := outerTurn_of_followsBoundary hw hM hf
  exact ⟨isNoncrossingClosedWalk_vertexJoin hw ht hx hy,
    followsBoundary_outerCycle _ hM' (outerTurn_vertexJoin hw ht hx hy)⟩

/-- **A restriction keeps a noncrossing closed walk whose outer cycle follows its boundary.** -/
theorem followsBoundary_outerCycle_map {M : CombMap.{u}} {N : CombMap.{v}} {ι : N.Dart ↪ M.Dart}
    (hι : M.IsRestriction N ι) {w : List N.Dart} (hw : IsNoncrossingClosedWalk N w)
    (hN : N.IsPlanar) (hf : (hw.outerCycle hN).FollowsBoundary) (hM : M.IsPlanar) :
    ∃ hw' : IsNoncrossingClosedWalk M (w.map ι), (hw'.outerCycle hM).FollowsBoundary :=
  ⟨isNoncrossingClosedWalk_map hι hw,
    followsBoundary_outerCycle _ hM (outerTurn_map hι (outerTurn_of_followsBoundary hw hN hf))⟩

#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.boundaryWalk_getElem
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.boundaryWalk_getLast_head
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.outerStep
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.turnsBack_of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.outerTurn_iff_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.followsBoundary_outerCycle_vertexJoin
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.followsBoundary_outerCycle_map

end GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk
