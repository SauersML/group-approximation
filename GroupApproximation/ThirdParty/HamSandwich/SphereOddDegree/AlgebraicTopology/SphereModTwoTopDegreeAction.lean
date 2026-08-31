import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch2IntegralDegreeAction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Branch2CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.ConstructModTwoTopClassComparison
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereOrientationPosFromMV
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoTopGeneratorData
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoCoeffBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereModTwoBockstein
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.TopCatBridge

/-!
# Prompt 05: degree action on the sphere mod-two top class

This file proves that every continuous self-map of `Sⁿ` acts on the top `F₂`
homology generator (constructed in Prompt 04) by the mod-two reduction of its
integer degree, then assembles the project's `SphereModTwoTopData` datum and
discharges the Branch-2 comparison `ModTwoTopClassComparison`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- Naturality of the coefficient bridge, in element form. -/
theorem coeffBridge_hom_naturality_apply (n : ℕ) {X Y : TopCat.{0}} (φ : X ⟶ Y)
    (z : homologyZMod2 X n) :
    ((coeffBridge n).hom.app Y).hom ((homologyPushZMod2 φ n).hom z)
      = ((singularHomologyCoeffZMod2 n).map φ).hom (((coeffBridge n).hom.app X).hom z) := by
  have h := (coeffBridge n).hom.naturality φ
  have h2 := congrArg
    (fun (m : (homZMod2Fun n ⋙ resZ2).obj X ⟶ (singularHomologyCoeffZMod2 n).obj Y) => m.hom z) h
  simpa only [ModuleCat.comp_apply] using h2

/-- Functoriality of the `F₂` homology pushforward: identity. -/
theorem homologyPushZMod2_id (n : ℕ) (X : TopCat.{0}) :
    homologyPushZMod2 (𝟙 X) n = 𝟙 (homologyZMod2 X n) :=
  (homZMod2Fun n).map_id X

/-- Functoriality of the `F₂` homology pushforward: composition. -/
theorem homologyPushZMod2_comp (n : ℕ) {X Y Z : TopCat.{0}} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    homologyPushZMod2 (φ ≫ ψ) n = homologyPushZMod2 φ n ≫ homologyPushZMod2 ψ n :=
  (homZMod2Fun n).map_comp φ ψ

/-- Main action theorem of Prompt 05.

The pushforward of every continuous self-map of `S^n` sends the Prompt 04
mod-two top generator to `(degree f mod 2)` times that generator. -/
theorem sphereModTwoTopGenerator_action
    (n : ℕ) (hn : 1 ≤ n)
    (f : C(Sphere n, Sphere n)) :
    (homologyPushZMod2 (TopCat.ofHom f) n).hom
        (construct_SphereModTwoTopGeneratorData n hn).g
      = (degreeOfIso (sphereTopHomologyIso_unconditional n hn) f : ZMod 2) •
        (construct_SphereModTwoTopGeneratorData n hn).g := by
  classical
  set e := sphereTopHomologyIso_unconditional n hn with he
  set d : ℤ := degreeOfIso e f with hd
  set g := (construct_SphereModTwoTopGeneratorData n hn).g with hg
  -- `w` is the reduced generator, transported to the project model over `TopCat.sphere n`.
  set w : homologyZMod2 (TopCat.sphere n) n :=
    ((coeffBridge n).inv.app (TopCat.sphere n)).hom (reducedTopGenerator e) with hw
  -- `Ψ w = reducedTopGenerator e`.
  have hΨw : ((coeffBridge n).hom.app (TopCat.sphere n)).hom w = reducedTopGenerator e := by
    have hid := Iso.inv_hom_id_app (coeffBridge n) (TopCat.sphere n)
    have h2 := congrArg
      (fun (m : (singularHomologyCoeffZMod2 n).obj (TopCat.sphere n)
          ⟶ (singularHomologyCoeffZMod2 n).obj (TopCat.sphere n)) =>
        m.hom (reducedTopGenerator e)) hid
    simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h2
  -- `w ≠ 0`.
  have hwne : w ≠ 0 := by
    intro h0
    apply reducedTopGenerator_ne_zero n hn
    rw [← hΨw, h0, map_zero]
  -- Action on `w` in the project model over `TopCat.sphere n`.
  have hcoeff : ((singularHomologyCoeffZMod2 n).map (toTopCatSphereSelfMap f)).hom
        (reducedTopGenerator e)
      = (d : ℤ) • reducedTopGenerator e := modTwo_action_on_reduced_top_generator e f
  have hactionS : (homologyPushZMod2 (toTopCatSphereSelfMap f) n).hom w = (d : ZMod 2) • w := by
    have hkey : ((coeffBridge n).hom.app (TopCat.sphere n)).hom
          ((homologyPushZMod2 (toTopCatSphereSelfMap f) n).hom w)
        = ((coeffBridge n).hom.app (TopCat.sphere n)).hom ((d : ℤ) • w) := by
      rw [coeffBridge_hom_naturality_apply n (toTopCatSphereSelfMap f) w, hΨw, hcoeff,
        map_zsmul, hΨw]
    have hinj : Function.Injective ((coeffBridge n).hom.app (TopCat.sphere n)).hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have hww := hinj hkey
    rw [hww, Int.cast_smul_eq_zsmul]
  -- Transport the action from `TopCat.sphere n` to `TopCat.of (Sphere n)`.
  set g0 : homologyZMod2 (TopCat.of (Sphere n)) n :=
    (homologyPushZMod2 (topCatSphereIso n).hom n).hom w with hg0
  have htrans : (homologyPushZMod2 (TopCat.ofHom f) n).hom g0 = (d : ZMod 2) • g0 := by
    have hcomm : (topCatSphereIso n).hom ≫ TopCat.ofHom f
        = toTopCatSphereSelfMap f ≫ (topCatSphereIso n).hom := by
      simp only [toTopCatSphereSelfMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hfun := congrArg (fun (ψ : TopCat.sphere n ⟶ TopCat.of (Sphere n)) =>
      (homologyPushZMod2 ψ n).hom w) hcomm
    simp only [homologyPushZMod2_comp, ModuleCat.comp_apply] at hfun
    rw [hg0, hfun, hactionS, map_smul]
  -- `g0 ≠ 0`.
  have hg0ne : g0 ≠ 0 := by
    intro h0
    apply hwne
    have hback : (homologyPushZMod2 (topCatSphereIso n).inv n).hom g0 = w := by
      rw [hg0, ← ModuleCat.comp_apply, ← homologyPushZMod2_comp, Iso.hom_inv_id,
        homologyPushZMod2_id, ModuleCat.id_apply]
    rw [← hback, h0, map_zero]
  -- `g0 = g` since the top homology is spanned by the nonzero `g`.
  have hg0g : g0 = g := by
    obtain ⟨a, ha⟩ := (construct_SphereModTwoTopGeneratorData n hn).spans g0
    rw [← hg] at ha
    have hane : a ≠ 0 := by
      rintro rfl; rw [zero_smul] at ha; exact hg0ne ha
    have ha1 : a = 1 := by
      fin_cases a
      · exact absurd rfl hane
      · rfl
    rw [ha, ha1, one_smul]
  rw [← hg0g, htrans]

/-- Main theorem of Prompt 05: build the existing Branch-2 datum from Prompt 04's
nonzero spanning generator and the degree-action theorem above. -/
def construct_SphereModTwoTopData
    (n : ℕ) (hn : 1 ≤ n) :
    SphereModTwoTopData (sphereTopHomologyIso_unconditional n hn) where
  g := (construct_SphereModTwoTopGeneratorData n hn).g
  g_ne := (construct_SphereModTwoTopGeneratorData n hn).g_ne
  spans := (construct_SphereModTwoTopGeneratorData n hn).spans
  action := sphereModTwoTopGenerator_action n hn

/-- Prompt 05 corollary: the mod-two top-class comparison is now unconditional in
positive dimensions. -/
theorem construct_ModTwoTopClassComparison_unconditional
    (n : ℕ) (hn : 1 ≤ n) :
    ModTwoTopClassComparison (sphereTopHomologyIso_unconditional n hn) :=
  modTwoTopClassComparison_of_data
    (sphereTopHomologyIso_unconditional n hn)
    (construct_SphereModTwoTopData n hn)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

