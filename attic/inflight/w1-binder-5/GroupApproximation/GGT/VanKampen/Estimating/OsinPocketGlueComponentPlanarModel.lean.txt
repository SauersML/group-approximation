import GroupApproximation.GGT.VanKampen.CombMapComponents
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArcLakeGlueModel
import GroupApproximation.Meta.AxiomGuard

/-!
# Calibration: the seam form of component planarity on the lake glue

A model test, before its proof, for w1-binder-6's `SeamGlueComponentPlanarStatement`
(`Estimating/OsinPocketGlueComponents.lean`): for seam data `S` between planar maps `M` and `X`, with
the faces off the kept set reclosed along the reversed seam cycle into a planar map, every component
of the glued map is planar.

The lake glue `OsinPocketFullArcLakeGlueModel.lakeSeam` glues the rose `M` into the faces `{Π, O}` off
the lake walk `[0,2]` along the reversed walk `[3,1]`.  The seam cycle does not follow its boundary,
and the glued map splits into two components (`glueMap_not_connected`).  This file checks every
hypothesis of the seam form there and its conclusion.

* The faces off the kept set are the side `{K}` of the walk, and its inner cycle `[0,2]` reads the
  reversed seam cycle (`rest_iff`, `reverse_seam_cycle`).
* `M` is planar, and so is the reclosing of `{K}` along `[0,2]`, from its Euler equality
  (`reclosed_rest_planar`, `OsinPocketKeptCellSection.lakeEulerBranch`).
* `planar_of_dartCount_two`: a connected map with two darts whose face rotation fixes both is planar.
* `componentOf_iff_side`, `component_dartCount`, `component_facePerm`: every component of the glued map
  is a pair `{m1, x3}` or `{m3, x1}` swapped by the vertex rotation, with every dart a face of its own.
* `lakeSeamComponentsPlanar`: the endpoint.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, "Hull's small cancellation theorem",
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel

open Surgery.MapCollapse Surgery.PocketGlue SimpleClosedWalkSides
open OsinPocketLakeModel (M planar isNoncrossingClosedWalk_lakeCycle innerCycle_lakeCycle)
open OsinPocketFullArcLakeModel (lakeWalk)
open OsinPocketFullArcLakeGlueModel (lakeSeam m1 m3 x1 x3 side glueDart_cases sigma_m1 sigma_m3
  sigma_x1 sigma_x3 glueFacePerm_m1 glueFacePerm_m3 glueFacePerm_x1 glueFacePerm_x3
  side_eq_of_eqvGen glueMap_not_connected)

universe v

/-! ## The hypotheses -/

/-- The faces off the kept set are the side of the lake walk. -/
theorem rest_iff (f : M.Face) : f ∈ sideFaces M lakeWalk ↔ f ∉ lakeSeam.faces :=
  ⟨fun hf hout => (mem_sideOutside_iff M lakeWalk f).mp hout hf,
    fun hf => Classical.byContradiction fun hno => hf ((mem_sideOutside_iff M lakeWalk f).mpr hno)⟩

/-- The inner cycle of the lake walk reads the reversed seam cycle. -/
theorem reverse_seam_cycle :
    ∃ k, lakeSeam.boundary.cycle.reverse.map M.alpha =
      (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle.rotate k :=
  ⟨0, by decide⟩

/-- **The reclosing of the side of the lake walk is planar**, from its Euler equality. -/
theorem reclosed_rest_planar :
    (reclosedMap M (sideFaces M lakeWalk)
      (isNoncrossingClosedWalk_lakeCycle.innerCycle planar)).IsPlanar :=
  ⟨reclosedMap_connected M (sideFaces M lakeWalk) (isNoncrossingClosedWalk_lakeCycle.innerCycle planar)
      planar.1,
    OsinPocketKeptCellSection.lakeEulerBranch.1.trans planar.2⟩

/-! ## Two-dart maps -/

/-- **A connected map with two darts whose face rotation fixes both is planar**: one vertex, one
edge and two faces. -/
theorem planar_of_dartCount_two {N : CombMap.{v}} (hd : N.dartCount = 2) (hconn : N.IsConnected)
    (hfix : ∀ d, N.facePerm d = d) : N.IsPlanar := by
  refine ⟨hconn, ?_⟩
  have hsig : ∀ d, N.sigma d = N.alpha d := fun d => by
    have h := hfix (N.alpha d)
    change N.sigma (N.alpha (N.alpha d)) = N.alpha d at h
    rwa [N.alpha_involutive] at h
  have hf : N.faceCount = 2 :=
    (Nat.card_congr (OrbitClassifier.orbitEquiv N.facePerm id id (fun d => congrArg id (hfix d))
      (fun _ => rfl) (fun d => Equiv.Perm.SameCycle.refl _ _))).trans hd
  have hv : N.vertexCount = 1 := by
    obtain ⟨a, -, -, -⟩ := Nat.card_eq_two_iff.mp hd
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun p q => ?_⟩, ⟨Quotient.mk'' a⟩⟩
    refine Quotient.inductionOn₂ p q fun d e => Quotient.sound ?_
    by_cases hde : e = d
    · subst hde
      exact Equiv.Perm.SameCycle.refl _ _
    · obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' d).mp hd
      have he : e = y := huniq e hde
      have hα : N.alpha d = y := huniq (N.alpha d) (N.alpha_fixedPointFree d)
      refine ⟨1, ?_⟩
      rw [zpow_one, hsig, hα, he]
  have he : N.edgeCount = 1 := by
    have h := N.dartCount_eq_two_mul_edgeCount
    omega
  unfold CombMap.eulerCharacteristic
  rw [hv, he, hf]
  norm_num

/-! ## The components of the glued map -/

/-- The component of a glued dart is the set of darts on its side. -/
theorem componentOf_iff_side (x g : lakeSeam.glueMap.Dart) :
    lakeSeam.glueMap.componentOf x g ↔ side g = side x := by
  refine ⟨fun h => (side_eq_of_eqvGen h).symm, fun h => ?_⟩
  rcases glueDart_cases x with rfl | rfl | rfl | rfl <;>
    rcases glueDart_cases g with rfl | rfl | rfl | rfl
  all_goals first
    | exact Relation.EqvGen.refl _
    | exact Relation.EqvGen.rel _ _ (Or.inr sigma_m1)
    | exact Relation.EqvGen.rel _ _ (Or.inr sigma_m3)
    | exact Relation.EqvGen.rel _ _ (Or.inr sigma_x1)
    | exact Relation.EqvGen.rel _ _ (Or.inr sigma_x3)
    | exact absurd h (by decide)

theorem sigma_ne (x : lakeSeam.glueMap.Dart) : lakeSeam.glueMap.sigma x ≠ x := by
  rcases glueDart_cases x with rfl | rfl | rfl | rfl
  · rw [sigma_m1]
    exact Sum.inr_ne_inl
  · rw [sigma_m3]
    exact Sum.inr_ne_inl
  · rw [sigma_x1]
    exact Sum.inl_ne_inr
  · rw [sigma_x3]
    exact Sum.inl_ne_inr

/-- **Every component of the glued map has two darts**: a dart and its vertex partner. -/
theorem component_dartCount (x : lakeSeam.glueMap.Dart) :
    (lakeSeam.glueMap.component x).dartCount = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨⟨x, lakeSeam.glueMap.componentOf_self x⟩,
    ⟨lakeSeam.glueMap.sigma x, Relation.EqvGen.rel _ _ (Or.inr rfl)⟩,
    fun h => sigma_ne x (congrArg Subtype.val h).symm, ?_⟩
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨g, hg⟩ := z
  have hs := (componentOf_iff_side x g).mp hg
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases glueDart_cases x with rfl | rfl | rfl | rfl <;>
    rcases glueDart_cases g with rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Subtype.ext sigma_m1.symm)
    | exact Or.inr (Subtype.ext sigma_m3.symm)
    | exact Or.inr (Subtype.ext sigma_x1.symm)
    | exact Or.inr (Subtype.ext sigma_x3.symm)
    | exact absurd hs (by decide)

/-- Every dart of the glued map is a face of its own. -/
theorem glueMap_facePerm_fix (g : lakeSeam.glueMap.Dart) : lakeSeam.glueMap.facePerm g = g := by
  rw [lakeSeam.glueMap_facePerm]
  rcases glueDart_cases g with rfl | rfl | rfl | rfl
  · exact glueFacePerm_m1
  · exact glueFacePerm_m3
  · exact glueFacePerm_x1
  · exact glueFacePerm_x3

theorem component_facePerm (x : lakeSeam.glueMap.Dart) (d : (lakeSeam.glueMap.component x).Dart) :
    (lakeSeam.glueMap.component x).facePerm d = d :=
  Subtype.ext (glueMap_facePerm_fix d.1)

/-- **Every component of the lake glue is planar.** -/
theorem component_planar (x : lakeSeam.glueMap.Dart) : (lakeSeam.glueMap.component x).IsPlanar :=
  planar_of_dartCount_two (component_dartCount x) (lakeSeam.glueMap.component_connected x)
    (component_facePerm x)

/-! ## The endpoint -/

/-- **The seam form of component planarity holds on the lake glue** (model test).  Every hypothesis
of `SeamGlueComponentPlanarStatement` holds for `lakeSeam`, with the faces off the kept set the side
of the lake walk and its inner cycle, the glued map is not connected, and every component is
planar. -/
def LakeSeamComponentsPlanarStatement : Prop :=
  (∀ f, f ∈ sideFaces M lakeWalk ↔ f ∉ lakeSeam.faces) ∧
    (∃ k, lakeSeam.boundary.cycle.reverse.map M.alpha =
      (isNoncrossingClosedWalk_lakeCycle.innerCycle planar).cycle.rotate k) ∧
    M.IsPlanar ∧
    (reclosedMap M (sideFaces M lakeWalk) (isNoncrossingClosedWalk_lakeCycle.innerCycle planar)).IsPlanar ∧
    ¬ lakeSeam.glueMap.IsConnected ∧
    ∀ x : lakeSeam.glueMap.Dart, (lakeSeam.glueMap.component x).IsPlanar

theorem lakeSeamComponentsPlanar : LakeSeamComponentsPlanarStatement :=
  ⟨rest_iff, reverse_seam_cycle, planar, reclosed_rest_planar, glueMap_not_connected,
    component_planar⟩

end GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel

end

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel.reclosed_rest_planar
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel.planar_of_dartCount_two
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel.component_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel.component_planar
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketGlueComponentPlanarModel.lakeSeamComponentsPlanar
