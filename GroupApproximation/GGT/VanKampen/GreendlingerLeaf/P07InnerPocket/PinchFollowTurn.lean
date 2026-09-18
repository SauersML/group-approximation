import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedNoncrossingSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionRotate
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-69: following the boundary is a local turn check

`enclosedFaceSetSuccOfNoncrossing` builds `EnclosedFaceSetSucc X (sideFaces X w) (invDarts X w)`
from `(hw.outerCycle X.planar).FollowsBoundary`.  This file shows that the `FollowsBoundary`
premise is the same as a local turn condition on the list `L = w.reverse.map α`,
`pinchFollow_OuterTurn`.  At every position `i`, rotating from `α L[i]`, the dart `L[i+1]` (read
cyclically) is reached before any dart of `walkKeep w`.

The reason is that the face class of an outside boundary dart lies in `sideOutside w`
(`pinchFollow_faceClass_sideOutside`).  A walk dart related to it would put its face on the side.
So `boundaryWalk_of_run` turns every such run into a boundary walk.  Conversely, a boundary walk of
`sideOutside w` skips only internal darts, and those are not `walkKeep`.

**LOUD: FALSE.**  "Noncrossing plus both reclosed Euler equalities implies
`outerCycle.FollowsBoundary`" is false.
* The lake model `OsinPocketMultipleEdgeLakeModel` (`pocketCycle_outerCycle_not_followsBoundary`)
  is noncrossing and satisfies both Euler equalities, but its outer cycle does not follow.
* Python checks (scratch `gl-p07-69/run_follow.py`) on random planar maps, over all noncrossing
  walks of length at most 6, found 2462 + 390 configurations with both equalities and a
  non-following outer cycle.  The Euler equalities never failed there: they carry no information
  for noncrossing walks.
* The same failure occurs inside the premise block of `PinchCase.RestStatement` at the map level
  (scratch `gl-p07-69/lake_grid.py`, where `Π_i` holds a lake of `K`): 150 empty-arc and 3
  nonempty-arc configurations.

So the turn condition has to be an input.  It is checked locally, one position at a time.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

/-- The face class of a dart based outside `w` stays outside `w`. -/
theorem pinchFollow_faceClass_sideOutside {M : CombMap.{v}} {w : List M.Dart} {y x : M.Dart}
    (hy : M.faceOf y ∈ sideOutside M w)
    (hx : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M w)) y x) :
    M.faceOf x ∈ sideOutside M w := by
  rw [mem_sideOutside_iff] at hy ⊢
  intro hxs
  obtain ⟨d, hd, hdx⟩ := (mem_sideFaces_iff M w x).mp hxs
  exact hy ((mem_sideFaces_iff M w y).mpr
    ⟨d, hd, Relation.EqvGen.trans _ _ _ hdx (Relation.EqvGen.symm _ _ hx)⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_faceClass_sideOutside

/-- A dart internal to `sideOutside w` is not on an edge of `w`. -/
theorem pinchFollow_not_keep_of_internal {M : CombMap.{v}} {w : List M.Dart} {x : M.Dart}
    (h : InternalDart M (sideOutside M w) x) : ¬ walkKeep M w x := by
  intro hk
  obtain ⟨h1, h2⟩ := h
  rcases (show x ∈ w ∨ M.alpha x ∈ w from hk) with hx | hx
  · exact (mem_sideOutside_iff M w _).mp h1
      ((mem_sideFaces_iff M w x).mpr ⟨x, hx, Relation.EqvGen.refl _⟩)
  · exact (mem_sideOutside_iff M w _).mp h2
      ((mem_sideFaces_iff M w (M.alpha x)).mpr ⟨M.alpha x, hx, Relation.EqvGen.refl _⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_not_keep_of_internal

/-- The boundary successor of the dart at position `i` is the dart at position `i + 1`. -/
theorem pinchFollow_boundaryPerm_getElem {M : CombMap.{v}} {faces : Finset M.Face}
    (B : BoundaryCycle M faces) (i : Fin B.cycle.length) :
    (B.boundaryPerm (B.positionEquiv i) : M.Dart) =
      B.cycle[(i.val + 1) % B.cycle.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)) := by
  classical
  rw [BoundaryCycle.boundaryPerm_apply_val]
  exact List.next_getElem B.cycle B.cycle_nodup i.val i.isLt

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_boundaryPerm_getElem

/-- **A boundary cycle follows its boundary if each position turns to the next one.**  The face
classes (for `keep`) of the cycle darts must lie in `faces`. -/
theorem pinchFollow_follows_of_turn {M : CombMap.{v}} {faces : Finset M.Face}
    (B : BoundaryCycle M faces) (keep : M.Dart → Prop)
    (hclass : ∀ y ∈ B.cycle, ∀ x, Relation.EqvGen (CombMap.FaceClassStep M keep) y x →
      M.faceOf x ∈ faces)
    (hturn : ∀ (i : ℕ) (hi : i < B.cycle.length), ∃ m, 0 < m ∧
      (M.sigma ^ m) (M.alpha B.cycle[i]) =
        B.cycle[(i + 1) % B.cycle.length]'(Nat.mod_lt _ (by omega)) ∧
      ∀ k, 0 < k → k < m → ¬ keep ((M.sigma ^ k) (M.alpha B.cycle[i]))) :
    B.FollowsBoundary := by
  intro d
  obtain ⟨i, rfl⟩ := B.positionEquiv.surjective d
  obtain ⟨m, hm, hme, hnk⟩ := hturn i.val i.isLt
  have hb := boundaryWalk_of_run M keep faces (B.cycle[i.val]'i.isLt) hm hnk
    (hclass _ (List.getElem_mem i.isLt))
  rw [hme] at hb
  rw [pinchFollow_boundaryPerm_getElem]
  exact hb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_follows_of_turn

/-- **The outer turn condition of a closed walk.**  Write `L = w.reverse.map α`, the outer cycle.
At each position `i`, some rotation `σ ^ m` with `0 < m` takes `α L[i]` to `L[i + 1]` (read
cyclically), and no earlier rotation `σ ^ k` with `0 < k < m` lands on an edge of `w`. -/
def pinchFollow_OuterTurn (M : CombMap.{v}) (w : List M.Dart) : Prop :=
  ∀ (i : ℕ) (hi : i < (w.reverse.map M.alpha).length), ∃ m, 0 < m ∧
    (M.sigma ^ m) (M.alpha ((w.reverse.map M.alpha)[i])) =
      (w.reverse.map M.alpha)[(i + 1) % (w.reverse.map M.alpha).length]'
        (Nat.mod_lt _ (by omega)) ∧
    ∀ k, 0 < k → k < m →
      ¬ walkKeep M w ((M.sigma ^ k) (M.alpha ((w.reverse.map M.alpha)[i])))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_OuterTurn

/-- The outer turn condition makes the outer cycle follow its boundary. -/
theorem pinchFollow_outer_follows {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) (hturn : pinchFollow_OuterTurn M w) :
    (hw.outerCycle hM).FollowsBoundary :=
  pinchFollow_follows_of_turn (hw.outerCycle hM) (walkKeep M w)
    (fun y hy _ hx =>
      pinchFollow_faceClass_sideOutside (((hw.outerCycle hM).cycle_mem_iff y).mp hy).1 hx)
    hturn

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_outer_follows

/-- **The outer cycle follows its boundary exactly when the outer turn condition holds.** -/
theorem pinchFollow_outer_follows_iff {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    (hw.outerCycle hM).FollowsBoundary ↔ pinchFollow_OuterTurn M w := by
  refine ⟨fun hf => ?_, pinchFollow_outer_follows hw hM⟩
  intro i hi
  have hb := hf ((hw.outerCycle hM).positionEquiv ⟨i, hi⟩)
  rw [pinchFollow_boundaryPerm_getElem, BoundaryCycle.positionEquiv_apply_val] at hb
  obtain ⟨m, hm, hme, hint⟩ := EnclosedNoncrossing.exists_sigma_pow_of_boundaryWalk hb
  exact ⟨m, hm, hme, fun k hk hkm => pinchFollow_not_keep_of_internal (hint k hk hkm)⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_outer_follows_iff

/-- **The side of a noncrossing walk is an enclosed face set with successor turns**, when the
exterior face is off its side and the outer turn condition holds. -/
theorem pinchFollow_enclosed_of_turn {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {walk : List X.toCombMap.Dart} (hw : IsNoncrossingClosedWalk X.toCombMap walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap walk)
    (hturn : pinchFollow_OuterTurn X.toCombMap walk) :
    EnclosedFaceSetSucc X (sideFaces X.toCombMap walk) (invDarts X walk) :=
  enclosedFaceSetSuccOfNoncrossing hw hout
    (pinchFollow_outer_follows hw X.planar hturn)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchFollow_enclosed_of_turn

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
