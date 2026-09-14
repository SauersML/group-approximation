import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.Meta.AxiomGuard

/-!
# A mixed touch: neither side of a noncrossing walk follows its boundary

Model test for the following clause of the two-gon copy walk (`TwoGonEitherFollowsCopyInput`,
`Estimating/OsinAppendixEulerTwoGonEitherFollowsCopy.lean`) and of the cell pocket walk
(`CellPocketWalkEitherFollowsStatement`, `Estimating/OsinPocketCellSideRelatorCell.lean`).  Both ask
that the outer or the inner cycle of a noncrossing closed walk follows its boundary.

A noncrossing walk touching itself at a vertex with two passes turns in one of two ways.
* The pinched two-gon (Configuration A, `OsinPocketPinchedTwoGonModel`): the side of the walk is
  pinched, so the inner cycle fails and the outer cycle follows.
* The lake (Configuration B, `OsinPocketLakeModel`): the side surrounds a lake, so the inner cycle
  follows and the outer cycle fails.

A walk with one touch of each kind has neither cycle following.  The smallest such map is a circle
with an outside bubble at one vertex and an inside loop at the other.  It has two vertices, four
edges (the top arc `{0,1}`, the bottom arc `{2,3}`, the bubble `{4,5}` and the loop `{6,7}`) and
four faces:
* the annulus `A = [0,6,2]`;
* the bubble `B = [4]`;
* the lake `L = [7]`;
* the outside `O = [1,5,3]`.
The walk `[0,6,2,4]` runs along the top arc, around the loop, along the bottom arc and around the
bubble.  Its side is `A ∪ B`, pinched at the bubble vertex, and it surrounds the lake at the loop
vertex.

* `isNoncrossingClosedWalk_mixedCycle`: the walk is a noncrossing closed walk.
* `mixedCycle_innerCycle_not_followsBoundary`: the step after `2` is `4`, but the face step from
  `2` is `0`, a boundary dart of the side.
* `mixedCycle_outerCycle_not_followsBoundary`: the step after `3` on the reversed walk `[5,3,7,1]`
  is `7`, but the face step from `3` is `1`, a boundary dart of the other side.
* `noncrossingMixedTouchModel`: a planar map with a noncrossing closed walk neither of whose
  boundary cycles follows.

So the disjunction does not follow from noncrossing alone.  A producer has to use the pocket
geometry to exclude a mixed touch, or split the walk at a touch.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketMixedTouchModel

open Equiv
open Surgery.MapCollapse (BoundaryWalk InternalDart)

def mixedAlpha : Perm (Fin 8) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide
  right_inv := by decide

def mixedSigma : Perm (Fin 8) where
  toFun := ![5, 6, 1, 0, 3, 4, 7, 2]
  invFun := ![3, 2, 7, 4, 5, 0, 1, 6]
  left_inv := by decide
  right_inv := by decide

/-- The circle with an outside bubble and an inside loop. -/
def M : CombMap where
  Dart := Fin 8
  dartFintype := inferInstance
  alpha := mixedAlpha
  sigma := mixedSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 8) n)

def faceClass : Fin 8 → Fin 4 := ![0, 1, 0, 1, 2, 1, 0, 3]
def faceRep : Fin 4 → Fin 8 := ![0, 1, 4, 7]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 1, 1, 0, 0, 0, 1, 1] : Fin 8 → Fin 2)
    (![0, 1] : Fin 2 → Fin 8) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 8, Relation.EqvGen M.Adjacent 0 d := by
      have h05 : Relation.EqvGen M.Adjacent 0 5 := .rel _ _ (Or.inr rfl)
      have h54 : Relation.EqvGen M.Adjacent 5 4 := .rel _ _ (Or.inr rfl)
      have h43 : Relation.EqvGen M.Adjacent 4 3 := .rel _ _ (Or.inr rfl)
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
      have h16 : Relation.EqvGen M.Adjacent 1 6 := .rel _ _ (Or.inr rfl)
      have h67 : Relation.EqvGen M.Adjacent 6 7 := .rel _ _ (Or.inr rfl)
      have h72 : Relation.EqvGen M.Adjacent 7 2 := .rel _ _ (Or.inr rfl)
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact .trans _ _ _ (.trans _ _ _ (.trans _ _ _ h01 h16) h67) h72
      · exact .trans _ _ _ (.trans _ _ _ h05 h54) h43
      · exact .trans _ _ _ h05 h54
      · exact h05
      · exact .trans _ _ _ h01 h16
      · exact .trans _ _ _ (.trans _ _ _ h01 h16) h67
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

/-- The mixed walk: top arc, loop, bottom arc, bubble. -/
abbrev mixedCycle : List M.Dart := [0, 6, 2, 4]

/-- One rotation step from the reversal of each dart of the walk reaches a dart of the walk. -/
theorem sigma_alpha_mem_mixedCycle :
    ∀ d ∈ mixedCycle, M.sigma (M.alpha d) ∈ mixedCycle := by
  decide

/-- **The mixed walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_mixedCycle : IsNoncrossingClosedWalk M mixedCycle where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide),
      List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩⟩⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_mixedCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- The face of `A` holding `0` lies on the side of the walk. -/
theorem faceOf_zero_mem_sideFaces :
    M.faceOf (0 : M.Dart) ∈ SimpleClosedWalkSides.sideFaces M mixedCycle :=
  ((isNoncrossingClosedWalk_mixedCycle.isBoundaryDart_sideFaces_iff planar 0).mpr (by decide)).1

/-- The dart `0` is a boundary dart of the side: its reversal `1` lies in the outside. -/
theorem not_internalDart_zero :
    ¬ InternalDart M (SimpleClosedWalkSides.sideFaces M mixedCycle) 0 := by
  rintro ⟨-, h⟩
  exact ((isNoncrossingClosedWalk_mixedCycle.isBoundaryDart_sideFaces_iff planar 0).mpr
    (by decide)).2 h

theorem innerCycle_mixedCycle_mem_two :
    (2 : M.Dart) ∈ (isNoncrossingClosedWalk_mixedCycle.innerCycle planar).cycle := by
  decide

theorem innerCycle_mixedCycle_next_two :
    ∀ hx : (2 : M.Dart) ∈ (isNoncrossingClosedWalk_mixedCycle.innerCycle planar).cycle,
      (isNoncrossingClosedWalk_mixedCycle.innerCycle planar).cycle.next 2 hx ≠ 0 := by
  decide

/-- **The inner cycle of the mixed walk does not follow its boundary**: pinched at the bubble
vertex. -/
theorem mixedCycle_innerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_mixedCycle.innerCycle planar).FollowsBoundary := by
  intro h
  have hw := h ⟨2, ((isNoncrossingClosedWalk_mixedCycle.innerCycle planar).cycle_mem_iff 2).mp
    innerCycle_mixedCycle_mem_two⟩
  rw [Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val] at hw
  change Relation.ReflTransGen _ (M.facePerm 2) _ at hw
  rw [show M.facePerm 2 = 0 by decide] at hw
  rcases Relation.ReflTransGen.cases_head hw with heq | ⟨c, ⟨hc, -⟩, -⟩
  · exact innerCycle_mixedCycle_next_two _ heq.symm
  · exact not_internalDart_zero hc

/-- The dart `1` of the outside is not internal to the other side: its reversal `0` lies in the
face of `A`. -/
theorem not_internalDart_one :
    ¬ InternalDart M (SimpleClosedWalkSides.sideOutside M mixedCycle) 1 := by
  rintro ⟨-, h⟩
  rw [show M.alpha 1 = 0 by decide, SimpleClosedWalkSides.mem_sideOutside_iff] at h
  exact h faceOf_zero_mem_sideFaces

theorem outerCycle_mixedCycle_mem_three :
    (3 : M.Dart) ∈ (isNoncrossingClosedWalk_mixedCycle.outerCycle planar).cycle := by
  decide

theorem outerCycle_mixedCycle_next_three :
    ∀ hx : (3 : M.Dart) ∈ (isNoncrossingClosedWalk_mixedCycle.outerCycle planar).cycle,
      (isNoncrossingClosedWalk_mixedCycle.outerCycle planar).cycle.next 3 hx ≠ 1 := by
  decide

/-- **The outer cycle of the mixed walk does not follow its boundary**: the lake at the loop
vertex. -/
theorem mixedCycle_outerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_mixedCycle.outerCycle planar).FollowsBoundary := by
  intro h
  have hw := h ⟨3, ((isNoncrossingClosedWalk_mixedCycle.outerCycle planar).cycle_mem_iff 3).mp
    outerCycle_mixedCycle_mem_three⟩
  rw [Surgery.MapCollapse.BoundaryCycle.boundaryPerm_apply_val] at hw
  change Relation.ReflTransGen _ (M.facePerm 3) _ at hw
  rw [show M.facePerm 3 = 1 by decide] at hw
  rcases Relation.ReflTransGen.cases_head hw with heq | ⟨c, ⟨hc, -⟩, -⟩
  · exact outerCycle_mixedCycle_next_three _ heq.symm
  · exact not_internalDart_one hc

/-- **A mixed touch** (model test): a planar map with a noncrossing closed walk neither of whose
boundary cycles follows its boundary.  So the clause "the outer or the inner cycle follows" does
not follow from noncrossing alone. -/
def NoncrossingMixedTouchModel : Prop :=
  ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (w : List N.Dart) (hw : IsNoncrossingClosedWalk N w),
    ¬ (hw.innerCycle hN).FollowsBoundary ∧ ¬ (hw.outerCycle hN).FollowsBoundary

theorem noncrossingMixedTouchModel : NoncrossingMixedTouchModel :=
  ⟨M, planar, mixedCycle, isNoncrossingClosedWalk_mixedCycle,
    mixedCycle_innerCycle_not_followsBoundary, mixedCycle_outerCycle_not_followsBoundary⟩

#audit_closed_axioms planar
#audit_closed_axioms isNoncrossingClosedWalk_mixedCycle
#audit_closed_axioms mixedCycle_innerCycle_not_followsBoundary
#audit_closed_axioms mixedCycle_outerCycle_not_followsBoundary
#audit_closed_axioms noncrossingMixedTouchModel

end GroupApproximation.GGT.VanKampen.OsinPocketMixedTouchModel
