import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchFirstTurn
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# First-turn order of a pocket is following on the complement side

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch step of binder 7 splits a vertex of a pocket face set in
first-turn order (`PocketFaceSet.FirstTurns`, `CellPocketFaceSet.FirstTurns`): the turn from each dart
`d` of the boundary cycle into the next dart `e` rotates from `e` to `alpha d` past darts off the
edges of the cycle.  The producers give a pocket in walk order, whose boundary cycle is a noncrossing
closed walk `w` (`PocketWalk.toPocketFaceSetOfNoncrossing`,
`CellPocketWalk.toCellPocketFaceSetOfNoncrossing`).

This module shows that for such a pocket, first-turn order is exactly the following of the outer
cycle `w.reverse.map alpha` on the other side of the walk.
* When the outer cycle follows its boundary, the successor of `alpha e` on it is the reversal of the
  walk dart before `e` (`IsNoncrossingClosedWalk.outerCycle_boundaryPerm_val`), and a boundary walk of
  the other side is a first turn (`FirstTurn.of_boundaryWalk`).
* Conversely a first-turn chain makes the outer cycle follow (`FirstTurnWalk.outerCycle_followsBoundary`).

So a producer of first-turn order has to deliver outer following.  On a lake, even with proper arcs
and the source cell inside the lake, no ordering of the boundary cycle is in first-turn order
(`OsinPocketCellFirstTurnsLakeModel.properLake_not_firstTurnOrder`), so the walk-order pocket alone
does not give it.

* `FirstTurnWalk.firstTurn_prev_of_outerFollows`: the first turn from `alpha e` onto the reversal of
  the walk dart before `e`.
* `FirstTurnWalk.firstTurnChain_of_outerFollows`, `FirstTurnWalk.outerFollows_of_firstTurnChain`: the
  chain condition of `FirstTurns` on the list `w`, and back.
* `PocketFaceSet.firstTurns_of_outerFollows`, `PocketFaceSet.firstTurns_iff_outerFollows`, and the same
  for `CellPocketFaceSet`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse SimpleClosedWalkSides

namespace FirstTurnWalk

variable {M : CombMap.{v}}

/-- **The turn onto the walk dart before.**  On a noncrossing closed walk whose outer cycle follows
its boundary, rotating from a walk dart `e` first meets an edge of the walk at the reversal of the
walk dart before `e`. -/
theorem firstTurn_prev_of_outerFollows [DecidableEq M.Dart] (hM : M.IsPlanar) {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) (hfollows : (hw.outerCycle hM).FollowsBoundary)
    {e : M.Dart} (he : e ∈ w) :
    FirstTurn M (w.reverse.map M.alpha) (M.alpha e) (M.alpha (w.prev e he)) := by
  have hbd : ∀ x ∈ w.reverse.map M.alpha, IsBoundaryDart M (sideOutside M w) x :=
    fun x hx => ((hw.outerCycle hM).cycle_mem_iff x).mp hx
  have hα : IsBoundaryDart M (sideOutside M w) (M.alpha e) :=
    (hw.isBoundaryDart_sideOutside_iff hM (M.alpha e)).mpr (by rw [M.alpha_involutive e]; exact he)
  have hwalk := hfollows ⟨M.alpha e, hα⟩
  rw [IsNoncrossingClosedWalk.outerCycle_boundaryPerm_val hw hM ⟨M.alpha e, hα⟩] at hwalk
  dsimp only at hwalk
  have hkey : ∀ (a : M.Dart) (ha : a ∈ w), a = e → w.prev a ha = w.prev e he := by
    rintro a ha rfl
    rfl
  rw [hkey _ _ (M.alpha_involutive e)] at hwalk
  exact FirstTurn.of_boundaryWalk hbd hwalk

/-- **Outer following gives the first-turn chain.**  On a noncrossing closed walk `w` whose outer
cycle follows its boundary, the turn from each walk dart `d` into the next dart `e`, and from the last
dart into the first, is a first turn from `alpha e` onto `alpha d`.  This is the condition
`PocketFaceSet.FirstTurns` on its boundary cycle. -/
theorem firstTurnChain_of_outerFollows (hM : M.IsPlanar) {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) (hfollows : (hw.outerCycle hM).FollowsBoundary) :
    w.IsChain (fun d e => FirstTurn M (w.reverse.map M.alpha) (M.alpha e) (M.alpha d)) ∧
      FirstTurn M (w.reverse.map M.alpha) (M.alpha (w.head hw.ne_nil))
        (M.alpha (w.getLast hw.ne_nil)) := by
  classical
  have hkey : ∀ (a b : M.Dart) (ha : a ∈ w) (hb : b ∈ w), a = b → w.prev a ha = w.prev b hb := by
    rintro a b ha hb rfl
    rfl
  refine ⟨List.isChain_iff_getElem.mpr fun i hi => ?_, ?_⟩
  · have hi' : i < w.length := by omega
    have hnext : w.next w[i] (List.getElem_mem hi') = w[i + 1] := by
      rw [List.next_getElem w hw.nodup i hi']
      simp [Nat.mod_eq_of_lt hi]
    have hprev : w.prev w[i + 1] (List.getElem_mem hi) = w[i] :=
      (hkey _ _ (List.getElem_mem hi) (List.next_mem ..) hnext.symm).trans
        (List.prev_next w hw.nodup w[i] (List.getElem_mem hi'))
    have h := firstTurn_prev_of_outerFollows hM hw hfollows (List.getElem_mem hi)
    rwa [hprev] at h
  · have hprev : w.prev (w.head hw.ne_nil) (List.head_mem hw.ne_nil) = w.getLast hw.ne_nil :=
      (hkey _ _ (List.head_mem hw.ne_nil) (List.next_mem ..)
          (List.next_getLast_eq_head w hw.ne_nil hw.nodup).symm).trans
        (List.prev_next w hw.nodup (w.getLast hw.ne_nil) (List.getLast_mem hw.ne_nil))
    have h := firstTurn_prev_of_outerFollows hM hw hfollows (List.head_mem hw.ne_nil)
    rwa [hprev] at h

/-- **The first-turn chain gives outer following.**  The converse of
`firstTurnChain_of_outerFollows`, through `FirstTurnWalk.outerCycle_followsBoundary` on the
complement spelling `w.reverse.map alpha`. -/
theorem outerFollows_of_firstTurnChain (hM : M.IsPlanar) {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w)
    (h : w.IsChain (fun d e => FirstTurn M (w.reverse.map M.alpha) (M.alpha e) (M.alpha d)) ∧
      FirstTurn M (w.reverse.map M.alpha) (M.alpha (w.head hw.ne_nil))
        (M.alpha (w.getLast hw.ne_nil))) :
    (hw.outerCycle hM).FollowsBoundary := by
  have hne : w.reverse.map M.alpha ≠ [] := by simpa using hw.ne_nil
  have hchain : (w.reverse.map M.alpha).IsChain (FirstTurn M (w.reverse.map M.alpha)) := by
    simp only [List.isChain_map, List.isChain_reverse]
    exact h.1
  have hclose : FirstTurn M (w.reverse.map M.alpha) ((w.reverse.map M.alpha).getLast hne)
      ((w.reverse.map M.alpha).head hne) := by
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    exact h.2
  have hw' : IsNoncrossingClosedWalk M ((w.reverse.map M.alpha).reverse.map M.alpha) := by
    rw [reverse_map_alpha_involutive]
    exact hw
  have htransfer : ∀ (w' : List M.Dart) (hw'' : IsNoncrossingClosedWalk M w'), w' = w →
      (hw''.outerCycle hM).FollowsBoundary → (hw.outerCycle hM).FollowsBoundary := by
    rintro w' hw'' rfl hfollows
    exact hfollows
  exact htransfer _ hw' (reverse_map_alpha_involutive w)
    (outerCycle_followsBoundary hM hchain hne hclose hw')

end FirstTurnWalk

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket whose outer cycle follows its boundary is in first-turn order.** -/
theorem firstTurns_of_outerFollows (K : PocketFaceSet D eps X lo hi)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle)
    (hfollows : (hw.outerCycle X.planar).FollowsBoundary) : K.FirstTurns :=
  FirstTurnWalk.firstTurnChain_of_outerFollows X.planar hw hfollows

/-- **First-turn order is outer following**, for a pocket whose boundary cycle is a noncrossing
closed walk. -/
theorem firstTurns_iff_outerFollows (K : PocketFaceSet D eps X lo hi)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle) :
    K.FirstTurns ↔ (hw.outerCycle X.planar).FollowsBoundary :=
  ⟨fun hK => FirstTurnWalk.outerFollows_of_firstTurnChain X.planar hw hK,
    K.firstTurns_of_outerFollows hw⟩

end PocketFaceSet

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A cell pocket whose outer cycle follows its boundary is in first-turn order.** -/
theorem firstTurns_of_outerFollows (K : CellPocketFaceSet D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle)
    (hfollows : (hw.outerCycle X.planar).FollowsBoundary) : K.FirstTurns :=
  FirstTurnWalk.firstTurnChain_of_outerFollows X.planar hw hfollows

/-- **First-turn order is outer following**, for a cell pocket whose boundary cycle is a noncrossing
closed walk. -/
theorem firstTurns_iff_outerFollows (K : CellPocketFaceSet D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle) :
    K.FirstTurns ↔ (hw.outerCycle X.planar).FollowsBoundary :=
  ⟨fun hK => FirstTurnWalk.outerFollows_of_firstTurnChain X.planar hw hK,
    K.firstTurns_of_outerFollows hw⟩

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.firstTurn_prev_of_outerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.firstTurnChain_of_outerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.outerFollows_of_firstTurnChain
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.firstTurns_of_outerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.firstTurns_iff_outerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.firstTurns_of_outerFollows
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.firstTurns_iff_outerFollows
