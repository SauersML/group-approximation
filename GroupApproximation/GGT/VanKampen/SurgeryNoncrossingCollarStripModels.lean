import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.GGT.VanKampen.SurgeryNoncrossingCollarWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Model tests for the noncrossing strip hypothesis

`NoncrossingCollarStrip.NoncrossingStripStatement` asks for a noncrossing closed walk whose outer
cycle follows its boundary.  By `NoncrossingCollarWalk.outerTurn_iff_followsBoundary` this is the
rotation condition `OuterTurn`.  Four walks test it.

* The pinched two-gon (`OsinPocketPinchedTwoGonModel`): the walk `[5,3,4,6]` visits a vertex
  twice and turns back (`outerTurn_pinchCycle`).
* The two-petal rose (`OsinPocketLakeModel.M`) with the walk `[1,3]` along both petals: the walk
  turns back and is not simple, and its first dart bounds a monogon
  (`monogonSideWithRestModel`).  This is the monogon side with a nonempty rest that
  `GeodesicCollar.stripSingleton` excludes and `NoncrossingCollarStrip.monogonStrip` handles.
* The lake `[0,2]` on the same rose does not turn back (`not_outerTurn_lakeCycle`).
* The three-petal rose (one vertex, three loops) with the walk `[0,2,4]` satisfies every field of
  `IsNoncrossingClosedWalk` but does not turn back, so its outer cycle does not follow its boundary
  (`roseCycle_outerCycle_not_followsBoundary`).

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636, "Hull's small cancellation theorem", through
Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels

open Equiv NoncrossingCollarWalk

/-- **The pinched two-gon turns back.** -/
theorem outerTurn_pinchCycle :
    OuterTurn OsinPocketPinchedTwoGonModel.diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) :=
  outerTurn_of_followsBoundary OsinPocketPinchedTwoGonModel.isNoncrossingClosedWalk_pinchCycle
    OsinPocketPinchedTwoGonModel.diagram.planar
    OsinPocketPinchedTwoGonModel.pinchCycle_outerCycle_followsBoundary

/-- **The lake does not turn back.** -/
theorem not_outerTurn_lakeCycle : ¬ OuterTurn OsinPocketLakeModel.M ([0, 2] : List (Fin 4)) :=
  fun h => OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary
    (followsBoundary_outerCycle OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle
      OsinPocketLakeModel.planar h)

/-- One rotation step from the reversal of each petal dart reaches a dart of the petal walk. -/
theorem sigma_alpha_mem_petalCycle :
    ∀ d ∈ ([1, 3] : List OsinPocketLakeModel.M.Dart),
      OsinPocketLakeModel.M.sigma (OsinPocketLakeModel.M.alpha d) ∈
        ([1, 3] : List OsinPocketLakeModel.M.Dart) := by
  decide

/-- **The petal walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_petalCycle :
    IsNoncrossingClosedWalk OsinPocketLakeModel.M ([1, 3] : List (Fin 4)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr
    ⟨OsinPocketLakeModel.vertexEquiv.injective (by decide), List.isChain_singleton _⟩
  closes := OsinPocketLakeModel.vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_petalCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The petal walk turns back**: one rotation step from each petal dart is the reversal of the
other. -/
theorem outerTurn_petalCycle : OuterTurn OsinPocketLakeModel.M ([1, 3] : List (Fin 4)) where
  chain := List.isChain_cons_cons.mpr
    ⟨⟨1, Nat.one_pos, by rw [pow_one]; decide,
        fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩,
      List.isChain_singleton _⟩
  closes _ := ⟨1, Nat.one_pos,
    show (OsinPocketLakeModel.M.sigma ^ 1) 1 = OsinPocketLakeModel.M.alpha 3 by
      rw [pow_one]; decide,
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩

/-- **The petal walk is not simple:** both darts start at the one vertex. -/
theorem petalCycle_not_isSimpleClosedWalk :
    ¬ IsSimpleClosedWalk OsinPocketLakeModel.M ([1, 3] : List (Fin 4)) := by
  intro h
  have hv : OsinPocketLakeModel.M.vertexOf (1 : OsinPocketLakeModel.M.Dart) =
      OsinPocketLakeModel.M.vertexOf (3 : OsinPocketLakeModel.M.Dart) :=
    OsinPocketLakeModel.vertexEquiv.injective (by decide)
  have hnodup := h.vertex_nodup
  change [OsinPocketLakeModel.M.vertexOf (1 : OsinPocketLakeModel.M.Dart),
    OsinPocketLakeModel.M.vertexOf (3 : OsinPocketLakeModel.M.Dart)].Nodup at hnodup
  rw [hv] at hnodup
  exact (List.nodup_cons.mp hnodup).1 (by simp)

/-- **A monogon side with a nonempty rest** (model test).  There is a planar map with a noncrossing
closed walk `d :: rest`, `rest ≠ []`, whose outer cycle follows its boundary, whose first dart
bounds a monogon, and which is not simple. -/
def MonogonSideWithRestModel : Prop :=
  ∃ (N : CombMap.{0}) (hN : N.IsPlanar) (d : N.Dart) (rest : List N.Dart)
    (hw : IsNoncrossingClosedWalk N (d :: rest)),
    rest ≠ [] ∧ N.facePerm d = d ∧ (hw.outerCycle hN).FollowsBoundary ∧
      ¬ IsSimpleClosedWalk N (d :: rest)

theorem monogonSideWithRestModel : MonogonSideWithRestModel :=
  ⟨OsinPocketLakeModel.M, OsinPocketLakeModel.planar, _, _, isNoncrossingClosedWalk_petalCycle,
    List.cons_ne_nil _ _, by decide,
    followsBoundary_outerCycle _ OsinPocketLakeModel.planar outerTurn_petalCycle,
    petalCycle_not_isSimpleClosedWalk⟩

/-- The reversal of the three-petal rose, `(0 1)(2 3)(4 5)`. -/
def threeRoseAlpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

/-- The rotation of the three-petal rose, `1 → 0 → 3 → 2 → 5 → 4 → 1`. -/
def threeRoseSigma : Perm (Fin 6) where
  toFun := ![3, 0, 5, 2, 1, 4]
  invFun := ![1, 4, 3, 0, 5, 2]
  left_inv := by decide
  right_inv := by decide

/-- The rose with three petals. -/
def threeRose : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := threeRoseAlpha
  sigma := threeRoseSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq threeRose.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat threeRose.Dart n := inferInstanceAs (OfNat (Fin 6) n)

/-- The faces are the three petals `{0}`, `{2}`, `{4}` and the outside `{1,3,5}`. -/
noncomputable def threeRoseFaceEquiv : threeRose.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv threeRose.facePerm (![0, 3, 1, 3, 2, 3] : Fin 6 → Fin 4)
    (![0, 2, 4, 1] : Fin 4 → Fin 6) (by decide) (by decide) (by decide)

noncomputable def threeRoseVertexEquiv : threeRose.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv threeRose.sigma (![0, 0, 0, 0, 0, 0] : Fin 6 → Fin 1)
    (![0] : Fin 1 → Fin 6) (by decide) (by decide) (by decide)

theorem threeRose_planar : threeRose.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen threeRose.Adjacent 0 d := by
      have h03 : Relation.EqvGen threeRose.Adjacent 0 3 := .rel _ _ (Or.inr rfl)
      have h32 : Relation.EqvGen threeRose.Adjacent 3 2 := .rel _ _ (Or.inr rfl)
      have h25 : Relation.EqvGen threeRose.Adjacent 2 5 := .rel _ _ (Or.inr rfl)
      have h54 : Relation.EqvGen threeRose.Adjacent 5 4 := .rel _ _ (Or.inr rfl)
      have h41 : Relation.EqvGen threeRose.Adjacent 4 1 := .rel _ _ (Or.inr rfl)
      have h02 := Relation.EqvGen.trans _ _ _ h03 h32
      have h05 := Relation.EqvGen.trans _ _ _ h02 h25
      have h04 := Relation.EqvGen.trans _ _ _ h05 h54
      intro d
      fin_cases d
      · exact .refl _
      · exact .trans _ _ _ h04 h41
      · exact h02
      · exact h03
      · exact h04
      · exact h05
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : threeRose.vertexCount = 1 := (Nat.card_congr threeRoseVertexEquiv).trans (by simp)
    have hf : threeRose.faceCount = 4 := (Nat.card_congr threeRoseFaceEquiv).trans (by simp)
    have hd : threeRose.dartCount = 6 := by simp [CombMap.dartCount, threeRose]
    have he := threeRose.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : threeRose.edgeCount = 3 := by omega
    rw [heq]
    norm_num

theorem sigma_alpha_mem_roseCycle :
    ∀ d ∈ ([0, 2, 4] : List threeRose.Dart),
      threeRose.sigma (threeRose.alpha d) ∈ ([0, 2, 4] : List threeRose.Dart) := by
  decide

/-- **The three-petal walk is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_roseCycle :
    IsNoncrossingClosedWalk threeRose ([0, 2, 4] : List (Fin 6)) where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨threeRoseVertexEquiv.injective (by decide),
    List.isChain_cons_cons.mpr ⟨threeRoseVertexEquiv.injective (by decide),
      List.isChain_singleton _⟩⟩
  closes := threeRoseVertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first Nat.one_pos
    (by rw [pow_one]; exact sigma_alpha_mem_roseCycle d hd)
    fun _ hk0 hk1 => absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))

/-- **The walk dart `2` does not turn back to `0`**: rotating from `2`, the dart `5` on the edge of
`4` comes before the reversal `1` of `0`. -/
theorem not_turnsBack_roseCycle : ¬ TurnsBack threeRose ([0, 2, 4] : List (Fin 6)) 0 2 := by
  rintro ⟨m, hm0, hm, hk⟩
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [pow_one] at hm
    exact absurd hm (by decide)
  refine hk 1 Nat.one_pos (by omega) ?_
  rw [pow_one]
  unfold SimpleClosedWalkSides.walkKeep
  decide

theorem not_outerTurn_roseCycle : ¬ OuterTurn threeRose ([0, 2, 4] : List (Fin 6)) :=
  fun h => not_turnsBack_roseCycle (List.isChain_cons_cons.mp h.chain).1

/-- **The outer cycle of the three-petal walk does not follow its boundary.** -/
theorem roseCycle_outerCycle_not_followsBoundary :
    ¬ (isNoncrossingClosedWalk_roseCycle.outerCycle threeRose_planar).FollowsBoundary :=
  fun h => not_outerTurn_roseCycle
    (outerTurn_of_followsBoundary isNoncrossingClosedWalk_roseCycle threeRose_planar h)

end GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels

#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.outerTurn_pinchCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.not_outerTurn_lakeCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.monogonSideWithRestModel
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.threeRose_planar
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.isNoncrossingClosedWalk_roseCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStripModels.roseCycle_outerCycle_not_followsBoundary
