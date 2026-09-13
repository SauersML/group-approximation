import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonNoncrossing
import GroupApproximation.Meta.AxiomGuard

/-!
# Model tests for the first-turn pocket inputs

`Estimating/OsinPocketFirstTurnWalk.lean` produces the four inputs of
`PocketRegion.ofNoncrossingClosedWalk` from a first-turn walk `c`, the complement spelling of the
pocket.  Three models test its hypotheses.

* **Configuration A** (`Estimating/OsinPocketPinchedTwoGonModel.lean`): the complement spelling
  `[9,8,0,1]` of the pinched two-gon is a first-turn walk, with two corners rotating past the
  internal edge `{2,7}`, and its side holds the exterior face.  Its reversed walk `[5,3,4,6]` is
  the pocket cycle, which is not simple, and the builder's pocket has face set `pinchFaces`.
* **The lake** (`Estimating/OsinPocketLakeModel.lean`): the lake walk `[0,2]` is noncrossing, and
  its outer cycle `[3,1]` does not follow its boundary (`lakeCycle_outerCycle_not_followsBoundary`).
  The first turn from `3` to `1` fails: the first rotation from the reversal of `3` is `3`, a dart
  of the walk.  So the hypotheses exclude the lake, as they must.
* **A pendant spur**: a loop at one vertex with a pendant edge on each side.  The trimmed
  complement spelling `[0]` is a first-turn walk, rotating past the outside spur, and the four
  inputs hold for it; the untrimmed facial spelling `[0,2,3]` uses the spur edge in both
  directions.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 1636,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel

open Equiv Surgery.MapCollapse SimpleClosedWalkSides
open OsinPocketPinchedTwoGonModel (diagram pinchFaces)

section PinchedTwoGon

theorem pinch_ne_nil : ([9, 8, 0, 1] : List (Fin 10)) ≠ [] := List.cons_ne_nil _ _

theorem pinch_nodup : ([9, 8, 0, 1] : List (Fin 10)).Nodup := by decide

theorem pinch_alpha_not_mem :
    ∀ x ∈ ([9, 8, 0, 1] : List diagram.toCombMap.Dart),
      diagram.toCombMap.alpha x ∉ ([9, 8, 0, 1] : List diagram.toCombMap.Dart) := by
  decide

/-- The first turns from `9` to `8` and from `0` to `1` are face steps; the first turn from `8`
to `0` rotates past the internal dart `7`. -/
theorem pinch_isChain :
    ([9, 8, 0, 1] : List (Fin 10)).IsChain
      (FirstTurn diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10))) :=
  List.isChain_cons_cons.mpr ⟨FirstTurn.of_sigma_alpha (by decide),
    List.isChain_cons_cons.mpr ⟨FirstTurn.of_sigma_sigma_alpha
      (by unfold SimpleClosedWalkSides.walkKeep; decide) (by decide),
      List.isChain_cons_cons.mpr ⟨FirstTurn.of_sigma_alpha (by decide),
        List.isChain_singleton _⟩⟩⟩

/-- The closing first turn from `1` to `9` rotates past the internal dart `2`. -/
theorem pinch_close : FirstTurn diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10)) 1 9 :=
  FirstTurn.of_sigma_sigma_alpha (by unfold SimpleClosedWalkSides.walkKeep; decide) (by decide)

/-- The exterior face `[7,9,8]` lies on the side of the complement spelling. -/
theorem pinch_outerFace_mem :
    diagram.outerFace ∈ sideFaces diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10)) := by
  show diagram.toCombMap.faceOf 7 ∈ _
  exact (mem_sideFaces_iff diagram.toCombMap _ 7).mpr
    ⟨8, by decide, .rel _ _ (Or.inl (by decide))⟩

theorem pinch_reverse_map_alpha :
    ([9, 8, 0, 1] : List (Fin 10)).reverse.map diagram.toCombMap.alpha =
      ([5, 3, 4, 6] : List (Fin 10)) := by
  decide

/-- **The walk the first-turn inputs certify on Configuration A is not simple.** -/
theorem pinch_walk_not_simple :
    ¬ IsSimpleClosedWalk diagram.toCombMap
      (([9, 8, 0, 1] : List (Fin 10)).reverse.map diagram.toCombMap.alpha) := fun h =>
  OsinPocketPinchedTwoGonModel.not_isSimpleClosedWalk
    ((congrArg (IsSimpleClosedWalk diagram.toCombMap) pinch_reverse_map_alpha).mp h)

/-- **The builder on Configuration A:** the pocket region of the complement spelling has face set
`pinchFaces`, the two digons. -/
theorem pinch_pocket_faces :
    (PocketRegion.ofFirstTurnWalk (Delta := diagram) (c := ([9, 8, 0, 1] : List (Fin 10)))
      pinch_ne_nil pinch_nodup pinch_alpha_not_mem pinch_isChain pinch_close
      pinch_outerFace_mem).faces = pinchFaces := by
  rw [PocketRegion.ofFirstTurnWalk_faces]
  exact (congrArg (sideFaces diagram.toCombMap) pinch_reverse_map_alpha).trans
    OsinPocketPinchedTwoGonModel.sideFaces_pinchCycle

end PinchedTwoGon

section Lake

/-- The complement spelling `[3,1]` reverses to the lake walk `[0,2]`. -/
theorem lake_reverse_map_alpha :
    ([3, 1] : List (Fin 4)).reverse.map OsinPocketLakeModel.M.alpha =
      ([0, 2] : List (Fin 4)) := by
  decide

/-- **The lake fails a first turn.**  The first rotation from the reversal of `3` is `3`, a dart
of the walk, and it is not `1`. -/
theorem lake_not_firstTurn : ¬ FirstTurn OsinPocketLakeModel.M ([3, 1] : List (Fin 4)) 3 1 := by
  rintro ⟨k, hk, hky, havoid⟩
  rcases Nat.lt_or_ge 1 k with h1 | h1
  · exact havoid 1 Nat.zero_lt_one h1 (by rw [pow_one]; exact Or.inl (by decide))
  · obtain rfl : k = 1 := by omega
    rw [pow_one] at hky
    exact absurd hky (by decide)

end Lake

namespace Spur

def spurAlpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def spurSigma : Perm (Fin 6) where
  toFun := ![4, 2, 0, 3, 1, 5]
  invFun := ![2, 4, 1, 3, 0, 5]
  left_inv := by decide
  right_inv := by decide

/-- A loop `{0,1}` at one vertex with a pendant edge on each side: the spur `{2,3}` in the face
`[0,2,3]` and the spur `{4,5}` in the face `[1,4,5]`. -/
def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := spurAlpha
  sigma := spurSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 2 := ![0, 1, 0, 0, 1, 1]
def faceRep : Fin 2 → Fin 6 := ![0, 1]

noncomputable def faceEquiv : M.Face ≃ Fin 2 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 3 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 1, 0, 2] : Fin 6 → Fin 3)
    (![0, 3, 5] : Fin 3 → Fin 6) (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inl rfl)
    have h04 : Relation.EqvGen M.Adjacent 0 4 := .rel _ _ (Or.inr rfl)
    have h12 : Relation.EqvGen M.Adjacent 1 2 := .rel _ _ (Or.inr rfl)
    have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inl rfl)
    have h45 : Relation.EqvGen M.Adjacent 4 5 := .rel _ _ (Or.inl rfl)
    have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact .trans _ _ _ h01 h12
      · exact .trans _ _ _ (.trans _ _ _ h01 h12) h23
      · exact h04
      · exact .trans _ _ _ h04 h45
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 3 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 2 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

theorem spur_nodup : ([0] : List (Fin 6)).Nodup := by decide

theorem spur_alpha_not_mem :
    ∀ x ∈ ([0] : List M.Dart), M.alpha x ∉ ([0] : List M.Dart) := by
  decide

/-- The closing first turn from `0` to `0` rotates past the outside spur dart `2`. -/
theorem spur_close : FirstTurn M ([0] : List (Fin 6)) 0 0 :=
  FirstTurn.of_sigma_sigma_alpha (by unfold SimpleClosedWalkSides.walkKeep; decide) (by decide)

/-- The untrimmed facial spelling `[0,2,3]` uses the spur edge in both directions. -/
theorem spur_untrimmed_alpha_mem :
    ¬ ∀ x ∈ ([0, 2, 3] : List M.Dart), M.alpha x ∉ ([0, 2, 3] : List M.Dart) := by
  decide

/-- **The four inputs on the pendant spur.** -/
theorem spur_pocketInputs :
    ∃ hw : IsNoncrossingClosedWalk M (([0] : List (Fin 6)).reverse.map M.alpha),
      (∀ f ∈ sideFaces M ([0] : List (Fin 6)),
        f ∉ sideFaces M (([0] : List (Fin 6)).reverse.map M.alpha)) ∧
        (hw.outerCycle planar).FollowsBoundary ∧
        (reclosedMap M (sideFaces M (([0] : List (Fin 6)).reverse.map M.alpha))
          (hw.innerCycle planar)).eulerCharacteristic = M.eulerCharacteristic :=
  firstTurnWalkPocketInputs M planar [0] (List.cons_ne_nil _ _) spur_nodup spur_alpha_not_mem
    (List.isChain_singleton _) spur_close

end Spur

/-- **The model tests of the first-turn pocket inputs.**  On Configuration A the complement
spelling `[9,8,0,1]` satisfies every hypothesis, its side holds the exterior face, and the walk it
certifies is not simple.  The lake's outer cycle `[3,1]`, the complement spelling of the lake walk
`[0,2]`, fails a first turn.  On the pendant spur the trimmed spelling `[0]` satisfies every
hypothesis and the untrimmed spelling `[0,2,3]` fails the edge condition. -/
def FirstTurnWalkModelStatement : Prop :=
  (([9, 8, 0, 1] : List (Fin 10)).Nodup ∧
      (∀ x ∈ ([9, 8, 0, 1] : List diagram.toCombMap.Dart),
        diagram.toCombMap.alpha x ∉ ([9, 8, 0, 1] : List diagram.toCombMap.Dart)) ∧
      ([9, 8, 0, 1] : List (Fin 10)).IsChain
        (FirstTurn diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10))) ∧
      FirstTurn diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10)) 1 9 ∧
      diagram.outerFace ∈ sideFaces diagram.toCombMap ([9, 8, 0, 1] : List (Fin 10)) ∧
      ¬ IsSimpleClosedWalk diagram.toCombMap
        (([9, 8, 0, 1] : List (Fin 10)).reverse.map diagram.toCombMap.alpha)) ∧
    (([3, 1] : List (Fin 4)).reverse.map OsinPocketLakeModel.M.alpha = ([0, 2] : List (Fin 4)) ∧
      ¬ FirstTurn OsinPocketLakeModel.M ([3, 1] : List (Fin 4)) 3 1) ∧
    ((([0] : List (Fin 6)).Nodup ∧
        (∀ x ∈ ([0] : List Spur.M.Dart), Spur.M.alpha x ∉ ([0] : List Spur.M.Dart)) ∧
        FirstTurn Spur.M ([0] : List (Fin 6)) 0 0) ∧
      ¬ ∀ x ∈ ([0, 2, 3] : List Spur.M.Dart),
        Spur.M.alpha x ∉ ([0, 2, 3] : List Spur.M.Dart))

theorem firstTurnWalkModel : FirstTurnWalkModelStatement :=
  ⟨⟨pinch_nodup, pinch_alpha_not_mem, pinch_isChain, pinch_close, pinch_outerFace_mem,
      pinch_walk_not_simple⟩,
    ⟨lake_reverse_map_alpha, lake_not_firstTurn⟩,
    ⟨⟨Spur.spur_nodup, Spur.spur_alpha_not_mem, Spur.spur_close⟩,
      Spur.spur_untrimmed_alpha_mem⟩⟩

end GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel.pinch_pocket_faces
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel.Spur.planar
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel.Spur.spur_pocketInputs
#audit_closed_axioms
  GroupApproximation.GGT.VanKampen.OsinPocketFirstTurnWalkModel.firstTurnWalkModel
