import GroupApproximation.GGT.VanKampen.CombMapComponents
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArcLakeGlueModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Calibration: the components of the split glued map of the lake seam

A model test for `CombMapComponents`, on w1-binder-6's glue model
`OsinPocketFullArcLakeGlueModel`.  There the glued map `lakeSeam.glueMap` has the four darts
`m1, m3` (the kept boundary darts `1` of `Π` and `3` of `O`) and `x1, x3` (the darts `1` and `3` of
the glued rose); the glued edges pair `m1 ↔ x3` and `m3 ↔ x1`, the vertex rotation swaps the same pairs,
and the hand invariant `side` separates `{m1, x3}` from `{m3, x1}` (`glueMap_not_connected`).

The component API recovers that split:

* `componentOf_m1_iff`: the component of `m1` is exactly the darts with `side = true`, namely
  `{m1, x3}`.
* `component_m1_connected`, `componentCompl_m1_connected`: the component of `m1` and the rest are
  both connected maps, so the glued map has exactly these two components.
* `glueComponents`: the endpoint `GlueComponentsStatement`, together with `glueMap_not_connected`.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, "Hull's small cancellation theorem",
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.CombMapComponentsGlueModel

open OsinPocketFullArcLakeGlueModel (lakeSeam m1 m3 x1 x3 side glueDart_cases sigma_m1 sigma_m3
  side_eq_of_eqvGen glueMap_not_connected)

/-- **The component of `m1` is `{m1, x3}`.** -/
theorem componentOf_m1_iff (g : lakeSeam.glueMap.Dart) :
    lakeSeam.glueMap.componentOf m1 g ↔ side g = true := by
  constructor
  · intro h
    exact (side_eq_of_eqvGen h).symm.trans (by decide)
  · intro hg
    rcases glueDart_cases g with rfl | rfl | rfl | rfl
    · exact lakeSeam.glueMap.componentOf_self m1
    · exact absurd hg (by decide)
    · exact absurd hg (by decide)
    · exact Relation.EqvGen.rel _ _ (Or.inr sigma_m1)

theorem not_componentOf_m1_m3 : ¬ lakeSeam.glueMap.componentOf m1 m3 :=
  fun h => absurd ((componentOf_m1_iff m3).mp h) (by decide)

/-- **The component of `m1` is connected.** -/
theorem component_m1_connected : (lakeSeam.glueMap.component m1).IsConnected :=
  lakeSeam.glueMap.component_connected m1

/-- **The rest, `{m3, x1}`, is connected.** -/
theorem componentCompl_m1_connected : (lakeSeam.glueMap.componentCompl m1).IsConnected := by
  refine lakeSeam.glueMap.restrict_connected _ _ _ not_componentOf_m1_m3 fun g hg => ?_
  rcases glueDart_cases g with rfl | rfl | rfl | rfl
  · exact absurd (lakeSeam.glueMap.componentOf_self m1) hg
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inr sigma_m3)
  · exact absurd ((componentOf_m1_iff x3).mpr (by decide)) hg

/-- **The glued map of the lake seam splits into the component of `m1` and a connected rest**
(model test of `CombMapComponents`). -/
def GlueComponentsStatement : Prop :=
  (∀ g, lakeSeam.glueMap.componentOf m1 g ↔ side g = true) ∧
    (lakeSeam.glueMap.component m1).IsConnected ∧
      (lakeSeam.glueMap.componentCompl m1).IsConnected ∧ ¬ lakeSeam.glueMap.IsConnected

theorem glueComponents : GlueComponentsStatement :=
  ⟨componentOf_m1_iff, component_m1_connected, componentCompl_m1_connected, glueMap_not_connected⟩

end GroupApproximation.GGT.VanKampen.CombMapComponentsGlueModel

end

#audit_axioms GroupApproximation.GGT.VanKampen.CombMapComponentsGlueModel.componentOf_m1_iff
#audit_axioms GroupApproximation.GGT.VanKampen.CombMapComponentsGlueModel.componentCompl_m1_connected
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CombMapComponentsGlueModel.glueComponents
