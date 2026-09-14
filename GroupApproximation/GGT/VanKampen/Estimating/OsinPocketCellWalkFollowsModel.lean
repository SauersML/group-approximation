import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeLakeModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonOuterFollows
import GroupApproximation.Meta.AxiomGuard

/-!
# Which boundary cycle of a noncrossing pocket walk follows its boundary: model tests

A model test for `CellPocketWalkEitherFollowsStatement` (`Estimating/OsinPocketCellSideRelatorCell`),
run before a proof: when a cell pocket walk is noncrossing, does its outer cycle or its inner cycle
follow its boundary?  At a vertex the walk passes twice, the side whose sector lies inside the two
passages follows there, and the other side does not (`OsinPocketPinchedTwoGonOuterFollows`).

* Calibration.
  - On the lake map of `OsinPocketMultipleEdgeLakeModel` the inner cycle follows and the outer
    cycle does not.
  - On the pinched two-gon of `OsinPocketPinchedTwoGonModel` the outer cycle follows and the inner
    cycle does not.
  - So neither clause alone holds on both, and the residual is a disjunction
    (`calibration_opposite_clauses`).
* The double touch.  A walk touching itself once in each way leaves neither clause.
  - The map has eight darts, the edges `{0,1}`, `{2,3}`, `{4,5}` and `{6,7}`, and two vertices: `A`
    with rotation `1 ↦ 0 ↦ 7 ↦ 2 ↦ 1` and `B` with rotation `3 ↦ 4 ↦ 5 ↦ 6 ↦ 3`.  Its four faces
    are the monogon `[0]`, the face `[2,4,6]`, the monogon `[5]` and the face `[1,7,3]`.  The loops
    `{0,1}` at `A` and `{4,5}` at `B` join the digon `{2,3}`, `{6,7}` between `A` and `B`.
  - The walk `[0,2,4,6]` is a noncrossing closed walk (`isNoncrossingClosedWalk_walk`): one
    rotation step from the reversal of each walk dart reaches the next walk dart.
  - Its side holds the monogon `[0]` on the walk dart `0`, so the inner cycle does not follow
    (`walk_innerCycle_not_followsBoundary`).  The other side holds the monogon `[5]` across the
    walk dart `4`, so the outer cycle does not follow (`walk_outerCycle_not_followsBoundary`).
  - `doubleTouchNeitherFollows`: there is a planar map with a noncrossing closed walk neither of
    whose boundary cycles follows its boundary.

So the disjunction is not a principle of noncrossing walks on planar maps.  A proof of
`CellPocketWalkEitherFollowsStatement` has to use the data of the two regions, the edge conditions or
least area.  The model has no labels, relator cells, regions or arcs, and whether a least-area
diagram with an optimal family carries such a walk is not decided here.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel

open Equiv SimpleClosedWalkSides
open Surgery.MapCollapse (BoundaryCycle IsBoundaryDart)

/-- **The two calibration maps satisfy opposite clauses.**  On the lake map the inner cycle of the
pocket walk follows its boundary and the outer cycle does not; on the pinched two-gon the outer
cycle follows and the inner cycle does not. -/
theorem calibration_opposite_clauses :
    ((OsinPocketMultipleEdgeLakeModel.isNoncrossingClosedWalk_pocketCycle.innerCycle
          OsinPocketMultipleEdgeLakeModel.planar).FollowsBoundary ∧
        ¬ (OsinPocketMultipleEdgeLakeModel.isNoncrossingClosedWalk_pocketCycle.outerCycle
          OsinPocketMultipleEdgeLakeModel.planar).FollowsBoundary) ∧
      ((OsinPocketPinchedTwoGonModel.isNoncrossingClosedWalk_pinchCycle.outerCycle
          OsinPocketPinchedTwoGonModel.diagram.planar).FollowsBoundary ∧
        ¬ (OsinPocketPinchedTwoGonModel.isNoncrossingClosedWalk_pinchCycle.innerCycle
          OsinPocketPinchedTwoGonModel.diagram.planar).FollowsBoundary) :=
  ⟨⟨OsinPocketMultipleEdgeLakeModel.pocketCycle_innerCycle_followsBoundary,
      OsinPocketMultipleEdgeLakeModel.pocketCycle_outerCycle_not_followsBoundary⟩,
    ⟨OsinPocketPinchedTwoGonModel.pinchCycle_outerCycle_followsBoundary,
      OsinPocketPinchedTwoGonModel.pinchCycle_innerCycle_not_followsBoundary⟩⟩

/-! ## The double touch -/

def touchAlpha : Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

def touchSigma : Perm (Fin 8) where
  toFun := ![7, 0, 1, 4, 5, 6, 3, 2]
  invFun := ![1, 2, 7, 6, 3, 4, 5, 0]
  left_inv := by decide
  right_inv := by decide

/-- The double touch. -/
def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := touchAlpha
  sigma := touchSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

def faceClass : Fin 8 → Fin 4 := ![0, 1, 2, 1, 2, 3, 2, 1]
def faceRep : Fin 4 → Fin 8 := ![0, 1, 2, 5]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 1, 1, 1, 1, 0] : Fin 8 → Fin 2)
    (![0, 3] : Fin 2 → Fin 8) (by decide) (by decide) (by decide)

/-- **The double touch is planar**: connected, with two vertices, four edges and four faces. -/
theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
      have h07 : Relation.EqvGen M.Adjacent 0 7 := .rel _ _ (Or.inr rfl)
      have h72 : Relation.EqvGen M.Adjacent 7 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
      have h34 : Relation.EqvGen M.Adjacent 3 4 := .rel _ _ (Or.inr rfl)
      have h45 : Relation.EqvGen M.Adjacent 4 5 := .rel _ _ (Or.inl rfl)
      have h56 : Relation.EqvGen M.Adjacent 5 6 := .rel _ _ (Or.inr rfl)
      have h02 : Relation.EqvGen M.Adjacent 0 2 := .trans _ _ _ h07 h72
      have h03 : Relation.EqvGen M.Adjacent 0 3 := .trans _ _ _ h02 h23
      have h04 : Relation.EqvGen M.Adjacent 0 4 := .trans _ _ _ h03 h34
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .trans _ _ _ h04 h45
      have h06 : Relation.EqvGen M.Adjacent 0 6 := .trans _ _ _ h05 h56
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
      · exact h07
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 2 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 8 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 4 := by omega
    rw [heq]
    norm_num

/-- One rotation step from the reversal of each walk dart reaches a walk dart. -/
theorem sigma_alpha_mem_walk :
    ∀ d ∈ ([0, 2, 4, 6] : List M.Dart), M.sigma (M.alpha d) ∈ ([0, 2, 4, 6] : List M.Dart) := by
  decide

/-- **The walk `[0,2,4,6]` is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_walk : IsNoncrossingClosedWalk M ([0, 2, 4, 6] : List (Fin 8)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
      List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩⟩⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_walk d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The inner cycle of the walk does not follow its boundary:** the walk dart `0` bounds the
monogon `[0]` on its side, and `2` is a second walk dart. -/
theorem walk_innerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_walk.innerCycle planar).FollowsBoundary :=
  OsinPocketMultipleEdgeLakeModel.not_followsBoundary_of_monogon _ (y := 0) (z := 2) (by decide)
    ((isNoncrossingClosedWalk_walk.isBoundaryDart_sideFaces_iff planar 0).mpr (by decide))
    ((isNoncrossingClosedWalk_walk.isBoundaryDart_sideFaces_iff planar 2).mpr (by decide))
    (by decide)

/-- **The outer cycle of the walk does not follow its boundary:** the dart `5`, across the walk dart
`4`, bounds the monogon `[5]` on the other side, and `7`, across the walk dart `6`, is a second
boundary dart there. -/
theorem walk_outerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_walk.outerCycle planar).FollowsBoundary :=
  OsinPocketMultipleEdgeLakeModel.not_followsBoundary_of_monogon _ (y := 5) (z := 7) (by decide)
    ((isNoncrossingClosedWalk_walk.isBoundaryDart_sideOutside_iff planar 5).mpr (by decide))
    ((isNoncrossingClosedWalk_walk.isBoundaryDart_sideOutside_iff planar 7).mpr (by decide))
    (by decide)

/-- **A noncrossing walk with neither boundary cycle following** (model test).  There is a planar
map with a noncrossing closed walk whose inner cycle does not follow its boundary and whose outer
cycle does not follow its boundary either. -/
def DoubleTouchNeitherFollows : Prop :=
  ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (w : List N.Dart) (hw : IsNoncrossingClosedWalk N w),
    ¬ (hw.innerCycle hN).FollowsBoundary ∧ ¬ (hw.outerCycle hN).FollowsBoundary

theorem doubleTouchNeitherFollows : DoubleTouchNeitherFollows :=
  ⟨M, planar, _, isNoncrossingClosedWalk_walk, walk_innerCycle_not_followsBoundary,
    walk_outerCycle_not_followsBoundary⟩

end GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.calibration_opposite_clauses
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.planar
#audit_closed_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.isNoncrossingClosedWalk_walk
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.walk_innerCycle_not_followsBoundary
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.walk_outerCycle_not_followsBoundary
#audit_closed_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketCellWalkFollowsModel.doubleTouchNeitherFollows
