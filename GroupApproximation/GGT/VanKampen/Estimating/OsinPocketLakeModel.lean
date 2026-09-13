import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonOuterFollows
import GroupApproximation.Meta.AxiomGuard

/-!
# A lake: the outer side of a pinched noncrossing walk does not follow its boundary

A model test for the prediction put to this lane in `notes/nm-swarm/reports/dgo-analytic.md`
("R2 with kh-ejz's `IsNoncrossingClosedWalk` as `Simple`"), Configuration B.

hull-respell's report describes a lake: the source cell `Π` lies in a lake, `K.faces` is an annulus
pinched at a vertex `v`, and `Π` lies in the inner complement component. The pocket sectors at `v`
lie inside the passages, so the prediction is that the inner cycle follows and the outer cycle does
not.

The smallest map with this shape is a rose with two petals. It has four darts, the edges `{0,1}`
and `{2,3}`, and one vertex with rotation `0 ↦ 1 ↦ 2 ↦ 3 ↦ 0`. Its three faces are `K = [0,2]`,
the lake `Π = [1]` and the outside `O = [3]`. The walk `[0,2]` passes twice through the vertex.

* It is a noncrossing closed walk (`isNoncrossingClosedWalk_lakeCycle`) and is not simple
  (`lakeCycle_not_isSimpleClosedWalk`).
* Its inner cycle follows: `0 ↦ 2` and `2 ↦ 0` are face steps of `K`
  (`lakeCycle_innerCycle_followsBoundary`).
* Its outer cycle `[3,1]` does not follow (`lakeCycle_outerCycle_not_followsBoundary`). The face
  step from `3` returns to `3`. The dart `3` is not internal to the outer side, because its reversal
  `2` lies in `K`.

The endpoint `noncrossingPinchSidesPrediction` records both halves of the prediction, the first half
coming from `Estimating/OsinPocketPinchedTwoGonOuterFollows.lean`.
* Configuration A, the pinched two-gon: a planar map with a noncrossing closed walk that is not
  simple, whose inner cycle fails and whose outer cycle follows.
* Configuration B, the lake: a second such map and walk, whose inner cycle follows and whose outer
  cycle fails.

So under the proposed `Simple`, Configuration B stays in the pinch Prop. The model tests the map
only, with no labels, relator cells or arcs.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketLakeModel

open Equiv
open Surgery.MapCollapse (BoundaryWalk InternalDart)

def roseAlpha : Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

def roseSigma : Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- The rose with two petals. -/
def M : CombMap where
  Dart := Fin 4
  dartFintype := inferInstance
  alpha := roseAlpha
  sigma := roseSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 4))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 4) n)

def faceClass : Fin 4 → Fin 3 := ![0, 1, 0, 2]
def faceRep : Fin 3 → Fin 4 := ![0, 1, 3]

noncomputable def faceEquiv : M.Face ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 0] : Fin 4 → Fin 1) (![0] : Fin 1 → Fin 4)
    (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 4, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
      have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact .trans _ _ _ h01 h12
      · exact .trans _ _ _ (.trans _ _ _ h01 h12) h23
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 3 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 4 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 2 := by omega
    rw [heq]
    norm_num

/-- One rotation step from the reversal of each dart of the lake walk reaches a dart of the
walk. -/
theorem sigma_alpha_mem_lakeCycle :
    ∀ d ∈ ([0, 2] : List M.Dart), M.sigma (M.alpha d) ∈ ([0, 2] : List M.Dart) := by
  decide

/-- **The lake walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_lakeCycle : IsNoncrossingClosedWalk M ([0, 2] : List (Fin 4)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_lakeCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The lake walk is not a simple closed walk:** both darts start at the one vertex. -/
theorem lakeCycle_not_isSimpleClosedWalk : ¬ IsSimpleClosedWalk M ([0, 2] : List (Fin 4)) := by
  intro h
  have hv : M.vertexOf (0 : M.Dart) = M.vertexOf (2 : M.Dart) := vertexEquiv.injective (by decide)
  have hnodup := h.vertex_nodup
  change [M.vertexOf (0 : M.Dart), M.vertexOf (2 : M.Dart)].Nodup at hnodup
  rw [hv] at hnodup
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- The face step `0 ↦ 2` of `K`. -/
theorem lakeWalk_zero_two (faces : Finset M.Face) : BoundaryWalk M faces 0 2 := by
  change Relation.ReflTransGen _ (M.facePerm 0) 2
  exact (show M.facePerm 0 = 2 by decide) ▸ Relation.ReflTransGen.refl

/-- The face step `2 ↦ 0` of `K`. -/
theorem lakeWalk_two_zero (faces : Finset M.Face) : BoundaryWalk M faces 2 0 := by
  change Relation.ReflTransGen _ (M.facePerm 2) 0
  exact (show M.facePerm 2 = 0 by decide) ▸ Relation.ReflTransGen.refl

theorem innerCycle_lakeCycle :
    (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle = ([0, 2] : List (Fin 4)) := by
  decide

theorem innerCycle_lakeCycle_getLast :
    (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle.getLast
      (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle_nonempty = 2 := by
  decide

theorem innerCycle_lakeCycle_head :
    (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle.head
      (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle_nonempty = 0 := by
  decide

/-- **The inner cycle of the lake walk follows its boundary.** -/
theorem lakeCycle_innerCycle_followsBoundary :
    (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).FollowsBoundary := by
  refine Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · rw [innerCycle_lakeCycle]
    exact List.isChain_cons_cons.mpr ⟨lakeWalk_zero_two _, List.isChain_singleton _⟩
  · rw [innerCycle_lakeCycle_getLast, innerCycle_lakeCycle_head]
    exact lakeWalk_two_zero _

theorem outerCycle_lakeCycle_mem_three :
    (3 : M.Dart) ∈ (isNoncrossingClosedWalk_lakeCycle.outerCycle planar).cycle := by
  decide

theorem outerCycle_lakeCycle_next_three :
    ∀ hx : (3 : M.Dart) ∈ (isNoncrossingClosedWalk_lakeCycle.outerCycle planar).cycle,
      (isNoncrossingClosedWalk_lakeCycle.outerCycle planar).cycle.next 3 hx ≠ 3 := by
  decide

/-- The face of `K` lies on the side of the lake walk. -/
theorem faceOf_two_mem_sideFaces :
    M.faceOf (2 : M.Dart) ∈ SimpleClosedWalkSides.sideFaces M ([0, 2] : List (Fin 4)) := by
  have h : M.faceOf (2 : M.Dart) ∈ SimpleClosedWalkSides.sideFaces M ([0, 2] : List (Fin 4)) ∧
      M.faceOf (M.alpha (2 : M.Dart)) ∉
        SimpleClosedWalkSides.sideFaces M ([0, 2] : List (Fin 4)) :=
    (isNoncrossingClosedWalk_lakeCycle.isBoundaryDart_sideFaces_iff planar 2).mpr (by decide)
  exact h.1

/-- The dart `3` of the outside is not internal to the outer side: its reversal `2` lies in the
face of `K`. -/
theorem not_internalDart_three :
    ¬ InternalDart M (SimpleClosedWalkSides.sideOutside M ([0, 2] : List (Fin 4))) 3 := by
  rintro ⟨-, h⟩
  rw [show M.alpha 3 = 2 by decide, SimpleClosedWalkSides.mem_sideOutside_iff] at h
  exact h faceOf_two_mem_sideFaces

/-- **The outer cycle of the lake walk does not follow its boundary.** -/
theorem lakeCycle_outerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_lakeCycle.outerCycle planar).FollowsBoundary := by
  intro h
  have hw := h ⟨3, ((isNoncrossingClosedWalk_lakeCycle.outerCycle planar).cycle_mem_iff 3).mp
    outerCycle_lakeCycle_mem_three⟩
  rw [Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val] at hw
  change Relation.ReflTransGen _ (M.facePerm 3) _ at hw
  rw [show M.facePerm 3 = 3 by decide] at hw
  rcases Relation.ReflTransGen.cases_head hw with heq | ⟨c, ⟨hc, -⟩, -⟩
  · exact outerCycle_lakeCycle_next_three _ heq.symm
  · exact not_internalDart_three hc

/-- **Both halves of the noncrossing sides prediction** (model test).
* There is a planar map with a noncrossing closed walk that is not simple, whose inner cycle does
  not follow its boundary and whose outer cycle does (Configuration A).
* There is another whose inner cycle follows and whose outer cycle does not (Configuration B). -/
def NoncrossingPinchSidesPrediction : Prop :=
  (∃ (N : CombMap.{0}) (hN : N.IsPlanar) (w : List N.Dart) (hw : IsNoncrossingClosedWalk N w),
      ¬ IsSimpleClosedWalk N w ∧ ¬ (hw.innerCycle hN).FollowsBoundary ∧
        (hw.outerCycle hN).FollowsBoundary) ∧
    ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (w : List N.Dart) (hw : IsNoncrossingClosedWalk N w),
      ¬ IsSimpleClosedWalk N w ∧ (hw.innerCycle hN).FollowsBoundary ∧
        ¬ (hw.outerCycle hN).FollowsBoundary

theorem noncrossingPinchSidesPrediction : NoncrossingPinchSidesPrediction :=
  ⟨⟨_, OsinPocketPinchedTwoGonModel.diagram.planar, _,
      OsinPocketPinchedTwoGonModel.isNoncrossingClosedWalk_pinchCycle,
      OsinPocketPinchedTwoGonModel.not_isSimpleClosedWalk,
      OsinPocketPinchedTwoGonModel.pinchCycle_innerCycle_not_followsBoundary,
      OsinPocketPinchedTwoGonModel.pinchCycle_outerCycle_followsBoundary⟩,
    ⟨M, planar, _, isNoncrossingClosedWalk_lakeCycle, lakeCycle_not_isSimpleClosedWalk,
      lakeCycle_innerCycle_followsBoundary, lakeCycle_outerCycle_not_followsBoundary⟩⟩

#audit_closed_axioms planar
#audit_closed_axioms isNoncrossingClosedWalk_lakeCycle
#audit_axioms lakeCycle_not_isSimpleClosedWalk
#audit_closed_axioms lakeCycle_innerCycle_followsBoundary
#audit_axioms not_internalDart_three
#audit_axioms lakeCycle_outerCycle_not_followsBoundary
#audit_closed_axioms noncrossingPinchSidesPrediction

end GroupApproximation.GGT.VanKampen.OsinPocketLakeModel
