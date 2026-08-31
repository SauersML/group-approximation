import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoefficientReduction
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality

/-!
# Coefficient-model bridge for singular homology

This file builds a natural isomorphism between two models of `F₂`-coefficient
singular homology of a topological space:

* the **coefficient-reduction model** `singularHomologyCoeffZMod2 n`
  (`CoefficientReduction.lean`), which is `Hₙ(-; ℤ-module ZMod 2)` living in
  `ModuleCat ℤ`; and
* the **project model** `homologyZMod2 (-) n` (`H1ClassifierZMod2.lean`), which is
  `Hₙ(-; ZMod 2)` living in `ModuleCat (ZMod 2)`.

The bridge is obtained from a general lemma: any additive functor `G` between
suitable module categories that preserves coproducts and homology commutes with
the singular homology functor.  Instantiating `G` with the restriction-of-scalars
functor `ModuleCat (ZMod 2) ⥤ ModuleCat ℤ` along `ℤ → ZMod 2` yields the desired
bridge (up to the transparent coefficient identification
`restrictScalars (ZMod 2) ≅ ℤ-module ZMod 2`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Functor

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-! ## A generic commutation of `singularHomologyFunctor` with a functor -/

section Generic

universe uC uD

variable {C : Type uC} [Category.{0} C] [HasCoproducts.{0} C] [Preadditive C]
  [CategoryWithHomology C]
variable {D : Type uD} [Category.{0} D] [HasCoproducts.{0} D] [Preadditive D]
  [CategoryWithHomology D]
variable (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
  [∀ (J : Type), PreservesColimitsOfShape (Discrete J) G]

/-- The component isomorphism used to build `sigmaConstCommIso` (reverse direction). -/
def sigmaConstCommComponent (M : C) (S : Type) :
    (Limits.sigmaConst.obj (G.obj M)).obj S ≅ (Limits.sigmaConst.obj M ⋙ G).obj S :=
  (PreservesCoproduct.iso G (fun _ : S => M)).symm

omit [Preadditive C] [CategoryWithHomology C] [Preadditive D] [CategoryWithHomology D]
  [G.Additive] [G.PreservesHomology] in
/-- Naturality square for the components of `sigmaConstCommComponent`. -/
theorem sigmaConstCommComponent_naturality (M : C) {S T : Type} (h : S ⟶ T) :
    (Limits.sigmaConst.obj (G.obj M)).map h ≫ (sigmaConstCommComponent G M T).hom
      = (sigmaConstCommComponent G M S).hom ≫ (Limits.sigmaConst.obj M ⋙ G).map h := by
  dsimp [sigmaConstCommComponent]
  ext j
  dsimp [Limits.sigmaConst]
  rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, ι_comp_sigmaComparison,
    ← Category.assoc, ι_comp_sigmaComparison, ← G.map_comp, Sigma.ι_comp_map', Category.id_comp]

/-- `G` commutes with the "constant coproduct" functor `sigmaConst`. -/
def sigmaConstCommIso (M : C) :
    (Limits.sigmaConst.obj M ⋙ G) ≅ Limits.sigmaConst.obj (G.obj M) :=
  (NatIso.ofComponents (sigmaConstCommComponent G M) (sigmaConstCommComponent_naturality G M)).symm

/-- `G` commutes with the `SSet`-level singular chain complex functor. -/
def sscf_comm (M : C) :
    (SSet.singularChainComplexFunctor.{0} C).obj M ⋙ G.mapHomologicalComplex (ComplexShape.down ℕ)
      ≅ (SSet.singularChainComplexFunctor.{0} D).obj (G.obj M) :=
  Functor.isoWhiskerLeft ((Limits.sigmaConst ⋙ SimplicialObject.whiskering (Type) C).obj M)
      (eqToIso (map_alternatingFaceMapComplex G)) ≪≫
    Functor.isoWhiskerRight ((SimplicialObject.whiskering (Type) D).mapIso (sigmaConstCommIso G M))
      (alternatingFaceMapComplex D)

/-- `G` commutes with the `TopCat`-level singular chain complex functor. -/
def scf_comm (M : C) :
    (singularChainComplexFunctor.{0} C).obj M ⋙ G.mapHomologicalComplex (ComplexShape.down ℕ)
      ≅ (singularChainComplexFunctor.{0} D).obj (G.obj M) :=
  Functor.isoWhiskerLeft TopCat.toSSet.{0} (sscf_comm G M)

omit [HasCoproducts C] [HasCoproducts D] [∀ (J : Type), PreservesColimitsOfShape (Discrete J) G] in
/-- Naturality square for the homology-preservation natural isomorphism. -/
theorem homBridge_naturality (n : ℕ) {K L : HomologicalComplex C (ComplexShape.down ℕ)} (φ : K ⟶ L) :
    ((G.mapHomologicalComplex (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φ
        ≫ (ShortComplex.mapHomologyIso (L.sc n) G).hom
      = (ShortComplex.mapHomologyIso (K.sc n) G).hom
        ≫ (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n ⋙ G).map φ := by
  convert ShortComplex.mapHomologyIso_hom_naturality (HomologicalComplex.shortComplexFunctor C (ComplexShape.down ℕ) n |>.map φ) G

/-- The homology-preservation natural isomorphism:
`G.mapHomologicalComplex ⋙ homologyFunctor ≅ homologyFunctor ⋙ G`. -/
def homBridgeNat (n : ℕ) :
    (G.mapHomologicalComplex (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
      ≅ HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n ⋙ G :=
  NatIso.ofComponents (fun K => ShortComplex.mapHomologyIso (K.sc n) G) (homBridge_naturality G n)

/-- **Generic commutation**: an additive functor preserving coproducts and homology
commutes with the singular homology functor. -/
def singularHomologyFunctor_comm (M : C) (n : ℕ) :
    (singularHomologyFunctor.{0} C n).obj M ⋙ G
      ≅ (singularHomologyFunctor.{0} D n).obj (G.obj M) :=
  Functor.isoWhiskerLeft ((singularChainComplexFunctor.{0} C).obj M) (homBridgeNat G n).symm ≪≫
    Functor.isoWhiskerRight (scf_comm G M)
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n)

end Generic

/-! ## The concrete coefficient bridge for `ZMod 2` -/

/-- Restriction of scalars along `ℤ → ZMod 2`. -/
abbrev resZ2 : ModuleCat.{0} (ZMod 2) ⥤ ModuleCat.{0} ℤ :=
  ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))

/-- The transparent identification `restrictScalars (ZMod 2) ≅ ℤ-module ZMod 2` at
the level of underlying `ℤ`-linear equivalences (the identity on `ZMod 2`). -/
def coeffModelLinEquiv :
    (resZ2.obj (ModuleCat.of (ZMod 2) (ZMod 2))) ≃ₗ[ℤ] (ZMod 2) where
  toFun := id
  map_add' := by intro x y; rfl
  map_smul' := by
    intro m x
    show (Int.castRingHom (ZMod 2) m) • x = m • x
    simp only [Int.coe_castRingHom]
    rw [Int.cast_smul_eq_zsmul]
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- The transparent coefficient identification `restrictScalars (ZMod 2) ≅ ℤ-module ZMod 2`. -/
def coeffModelIso : resZ2.obj (ModuleCat.of (ZMod 2) (ZMod 2)) ≅ ModuleCat.of ℤ (ZMod 2) :=
  coeffModelLinEquiv.toModuleIso

/-- The project's `F₂` singular homology, as a functor `TopCat ⥤ ModuleCat (ZMod 2)`.
On objects it is `homologyZMod2 (-) n`; on morphisms it is `homologyPushZMod2 (-) n`. -/
abbrev homZMod2Fun (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} (ZMod 2) :=
  (singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) n).obj (ModuleCat.of (ZMod 2) (ZMod 2))

/-- **The coefficient-model bridge.** A natural isomorphism between the project's
`F₂` homology (restricted to `ℤ`) and the coefficient-reduction model of `F₂`
homology. -/
def coeffBridge (n : ℕ) : homZMod2Fun n ⋙ resZ2 ≅ singularHomologyCoeffZMod2 n :=
  singularHomologyFunctor_comm resZ2 (ModuleCat.of (ZMod 2) (ZMod 2)) n ≪≫
    (singularHomologyFunctor (ModuleCat.{0} ℤ) n).mapIso coeffModelIso

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
