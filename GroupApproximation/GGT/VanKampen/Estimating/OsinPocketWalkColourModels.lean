import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchedTwoGonNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk colour step on the pinched two-gon and on the lake

A model test for `PocketWalkColour.orient_of_sides`, the last step of `pocketWalkColour`
(parity route, step (C)).

* The pinched two-gon (`OsinPocketPinchedTwoGonModel`) has the relator cell `Π = face 0`, the
  digons `a = face 1` and `b = face 2`, the outer face `face 3`, and the noncrossing walk
  `[5,3,4,6]`.  The test takes `A = {a}` only, so the darts `5` and `6` of `b` are covered by the
  second alternative: they cross into `Π` and into the outer face, like the gap darts of a pocket
  walk.  The walk crosses from `Π` into `a` at `3` and from `a` into the outer face at `4`.
* The lake (`OsinPocketLakeModel`) is the two-petal rose with faces `K = [0,2]`, the lake
  `Π = [1]` and the outside `O = [3]`, and the noncrossing walk `[0,2]`, which is not simple.  The
  walk crosses from `K` into the lake at `0` and into the outside at `2`.

On both maps a two-colouring changing colour exactly across the walk exists
(`ClosedWalkFaceColouring.exists_faceSet_colouring`), every such colouring gives the walk darts one
colour, and so the walk is the boundary cycle of a face set
(`ClosedWalkFaceColouring.exists_boundaryCycle_of_orient`).  The hypotheses of the colour step are
satisfiable and its conclusion feeds the boundary cycle.  The maps carry no section family, so the
diagram-level hypotheses of `PocketWalkColour.walk_orient` are not tested here.

## Manuscript status

Model test for infrastructure of `thm:hull` ("Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels

open SimpleClosedWalkSides

section Pinch

open OsinPocketPinchedTwoGonModel

/-- **The pinched two-gon walk carries one colour.** -/
theorem pinch_orient (faces : Finset diagram.toCombMap.Face)
    (hcol : ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d) :
    ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), ∀ e ∈ ([5, 3, 4, 6] : List (Fin 10)),
      (diagram.toCombMap.faceOf d ∈ faces ↔ diagram.toCombMap.faceOf e ∈ faces) := by
  have hface : ∀ (d : diagram.toCombMap.Dart) (i : Fin 4), faceClass d = i →
      diagram.toCombMap.faceOf d = face i := fun d i h => (faceOf_eq_face d i).mpr h
  have k3 := (hcol 3).mpr (Or.inl (by decide))
  have k4 := (hcol 4).mpr (Or.inl (by decide))
  rw [hface (diagram.toCombMap.alpha 3) 0 (by decide), hface 3 1 (by decide)] at k3
  rw [hface (diagram.toCombMap.alpha 4) 3 (by decide), hface 4 1 (by decide)] at k4
  have hcover : ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), diagram.toCombMap.faceOf d = face 1 ∨
      (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) = face 0 ∨
        diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) = face 3) := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (hface _ 0 (by decide)))
    · exact Or.inl (hface _ 1 (by decide))
    · exact Or.inl (hface _ 1 (by decide))
    · exact Or.inr (Or.inr (hface _ 3 (by decide)))
  refine PocketWalkColour.orient_of_sides hcol (A := fun f => f = face 1)
    (B := fun g => g = face 0 ∨ g = face 3) hcover ?_ (f₀ := face 1) rfl (Or.inl rfl)
  rintro f g rfl (rfl | rfl)
  · exact fun h => k3 h.symm
  · exact fun h => k4 h.symm

theorem pinch_exists_colouring : ∃ faces : Finset diagram.toCombMap.Face,
    ∀ d, ¬ (diagram.toCombMap.faceOf (diagram.toCombMap.alpha d) ∈ faces ↔
      diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d :=
  ClosedWalkFaceColouring.exists_faceSet_colouring diagram.planar
    isNoncrossingClosedWalk_pinchCycle.ne_nil isNoncrossingClosedWalk_pinchCycle.nodup
    isNoncrossingClosedWalk_pinchCycle.alpha_not_mem isNoncrossingClosedWalk_pinchCycle.chain
    isNoncrossingClosedWalk_pinchCycle.closes

theorem pinch_exists_boundaryCycle : ∃ (faces : Finset diagram.toCombMap.Face)
    (B : Surgery.MapCollapse.BoundaryCycle diagram.toCombMap faces),
      B.cycle = ([5, 3, 4, 6] : List (Fin 10)) :=
  ClosedWalkFaceColouring.exists_boundaryCycle_of_orient diagram.planar
    isNoncrossingClosedWalk_pinchCycle.ne_nil isNoncrossingClosedWalk_pinchCycle.nodup
    isNoncrossingClosedWalk_pinchCycle.alpha_not_mem isNoncrossingClosedWalk_pinchCycle.chain
    isNoncrossingClosedWalk_pinchCycle.closes pinch_orient

end Pinch

section Lake

open OsinPocketLakeModel

/-- **The lake walk carries one colour.** -/
theorem lake_orient (faces : Finset M.Face)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([0, 2] : List (Fin 4)) d) :
    ∀ d ∈ ([0, 2] : List (Fin 4)), ∀ e ∈ ([0, 2] : List (Fin 4)),
      (M.faceOf d ∈ faces ↔ M.faceOf e ∈ faces) := by
  have e2 : M.faceOf 2 = M.faceOf 0 := faceEquiv.injective (by decide)
  have k0 := (hcol 0).mpr (Or.inl (by decide))
  have k2 := (hcol 2).mpr (Or.inl (by decide))
  rw [show M.alpha 0 = 1 by decide] at k0
  rw [show M.alpha 2 = 3 by decide, e2] at k2
  have hcover : ∀ d ∈ ([0, 2] : List (Fin 4)), M.faceOf d = M.faceOf 0 ∨
      (M.faceOf (M.alpha d) = M.faceOf 1 ∨ M.faceOf (M.alpha d) = M.faceOf 3) := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl e2
  refine PocketWalkColour.orient_of_sides hcol (A := fun f => f = M.faceOf 0)
    (B := fun g => g = M.faceOf 1 ∨ g = M.faceOf 3) hcover ?_ (f₀ := M.faceOf 0) rfl (Or.inl rfl)
  rintro f g rfl (rfl | rfl)
  · exact fun h => k0 h.symm
  · exact fun h => k2 h.symm

theorem lake_exists_colouring : ∃ faces : Finset M.Face,
    ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔
      walkKeep M ([0, 2] : List (Fin 4)) d :=
  ClosedWalkFaceColouring.exists_faceSet_colouring planar
    isNoncrossingClosedWalk_lakeCycle.ne_nil isNoncrossingClosedWalk_lakeCycle.nodup
    isNoncrossingClosedWalk_lakeCycle.alpha_not_mem isNoncrossingClosedWalk_lakeCycle.chain
    isNoncrossingClosedWalk_lakeCycle.closes

theorem lake_exists_boundaryCycle : ∃ (faces : Finset M.Face)
    (B : Surgery.MapCollapse.BoundaryCycle M faces), B.cycle = ([0, 2] : List (Fin 4)) :=
  ClosedWalkFaceColouring.exists_boundaryCycle_of_orient planar
    isNoncrossingClosedWalk_lakeCycle.ne_nil isNoncrossingClosedWalk_lakeCycle.nodup
    isNoncrossingClosedWalk_lakeCycle.alpha_not_mem isNoncrossingClosedWalk_lakeCycle.chain
    isNoncrossingClosedWalk_lakeCycle.closes lake_orient

end Lake

/-- **Model test of the pocket walk colour step.**  On the pinched two-gon and on the lake, the
walk has a two-colouring changing colour exactly across it, every such colouring gives the faces of
all walk darts one colour, and the walk is the boundary cycle of a face set. -/
def PocketWalkColourModelTest : Prop :=
  ((∃ faces : Finset OsinPocketPinchedTwoGonModel.diagram.toCombMap.Face,
      ∀ d, ¬ (OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf
          (OsinPocketPinchedTwoGonModel.diagram.toCombMap.alpha d) ∈ faces ↔
          OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep OsinPocketPinchedTwoGonModel.diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10)) d) ∧
    (∀ faces : Finset OsinPocketPinchedTwoGonModel.diagram.toCombMap.Face,
      (∀ d, ¬ (OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf
          (OsinPocketPinchedTwoGonModel.diagram.toCombMap.alpha d) ∈ faces ↔
          OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf d ∈ faces) ↔
        walkKeep OsinPocketPinchedTwoGonModel.diagram.toCombMap ([5, 3, 4, 6] : List (Fin 10))
          d) →
      ∀ d ∈ ([5, 3, 4, 6] : List (Fin 10)), ∀ e ∈ ([5, 3, 4, 6] : List (Fin 10)),
        (OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf d ∈ faces ↔
          OsinPocketPinchedTwoGonModel.diagram.toCombMap.faceOf e ∈ faces)) ∧
    ∃ (faces : Finset OsinPocketPinchedTwoGonModel.diagram.toCombMap.Face)
      (B : Surgery.MapCollapse.BoundaryCycle OsinPocketPinchedTwoGonModel.diagram.toCombMap
        faces),
      B.cycle = ([5, 3, 4, 6] : List (Fin 10))) ∧
  (∃ faces : Finset OsinPocketLakeModel.M.Face,
      ∀ d, ¬ (OsinPocketLakeModel.M.faceOf (OsinPocketLakeModel.M.alpha d) ∈ faces ↔
          OsinPocketLakeModel.M.faceOf d ∈ faces) ↔
        walkKeep OsinPocketLakeModel.M ([0, 2] : List (Fin 4)) d) ∧
    (∀ faces : Finset OsinPocketLakeModel.M.Face,
      (∀ d, ¬ (OsinPocketLakeModel.M.faceOf (OsinPocketLakeModel.M.alpha d) ∈ faces ↔
          OsinPocketLakeModel.M.faceOf d ∈ faces) ↔
        walkKeep OsinPocketLakeModel.M ([0, 2] : List (Fin 4)) d) →
      ∀ d ∈ ([0, 2] : List (Fin 4)), ∀ e ∈ ([0, 2] : List (Fin 4)),
        (OsinPocketLakeModel.M.faceOf d ∈ faces ↔ OsinPocketLakeModel.M.faceOf e ∈ faces)) ∧
    ∃ (faces : Finset OsinPocketLakeModel.M.Face)
      (B : Surgery.MapCollapse.BoundaryCycle OsinPocketLakeModel.M faces),
      B.cycle = ([0, 2] : List (Fin 4))

theorem pocketWalkColourModelTest : PocketWalkColourModelTest :=
  ⟨⟨pinch_exists_colouring, pinch_orient, pinch_exists_boundaryCycle⟩,
    lake_exists_colouring, lake_orient, lake_exists_boundaryCycle⟩

end GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.pinch_orient
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.pinch_exists_colouring
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.pinch_exists_boundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.lake_orient
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.lake_exists_colouring
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.lake_exists_boundaryCycle
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketWalkColourModels.pocketWalkColourModelTest
