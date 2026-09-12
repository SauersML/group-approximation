import GroupApproximation.CharClass.CohomologyClassOf

/-!
# The Mayer–Vietoris connecting map from a lift, over any coefficient ring

The coefficient-generic forms of `CohomologyDeltaLift` and `CohomologyClassOf`.

* `CohClass.clsOfK` is the class of a cocycle of an arbitrary cochain complex of
  `R`-modules; it agrees with `cocycleClassK` on the singular cochain complex, it is
  surjective, and a cochain map sends the class of a cocycle to the class of its image.
* `MVDelta.delta_applyOf` specialises Mathlib's `ShortComplex.ShortExact.δ_apply` to the
  generic Mayer–Vietoris short exact sequence `mvCoSCOf K`: lift a cocycle `x₃` along `g`
  to any `x₂`, differentiate, descend along `f` to any `x₁`; then `δ [x₃] = [x₁]`.

Nothing here has a sign: the description of `δ` is sign-free over any ring, and the signs
of the Mayer–Vietoris sequence live in `g` (`MayerVietorisPullOf.mvCxInclVOf_comp_g`).
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace CohClass

variable {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat.{0} R) ℕ}

/-- The class in `H^n(C)` of a cocycle of `C`, over any coefficient ring. -/
def clsOfK (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (z : C.X n)
    (hz : (C.d n (n + 1)).hom z = 0) : C.homology n :=
  (C.homologyπ n).hom (C.cyclesMk z (n + 1) (ComplexShape.next_eq' _ (upRel n)) hz)

/-- For the singular cochain complex of a space this is `cocycleClassK`. -/
theorem clsOfK_eq_cocycleClassK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (z : singularCochainGroup K X n) (hz : cochainCoboundary K X n z = 0) :
    clsOfK (cochainCxK K X) n z hz = cocycleClassK K X n z hz := rfl

/-- The image of a cycle under `iCycles` is a cocycle. -/
theorem d_iCyclesK (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (c : C.cycles n) : (C.d n (n + 1)).hom ((C.iCycles n).hom c) = 0 := by
  have h := C.iCycles_d n (n + 1)
  change ((C.iCycles n ≫ C.d n (n + 1)).hom c) = 0
  rw [h]
  rfl

/-- **Every class is the class of a cocycle.** -/
theorem clsOfK_surjective (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (a : C.homology n) :
    ∃ (z : C.X n) (hz : (C.d n (n + 1)).hom z = 0), clsOfK C n z hz = a := by
  have hepi : Function.Surjective ((C.homologyπ n).hom) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  refine ⟨(C.iCycles n).hom c, d_iCyclesK C n c, ?_⟩
  rw [clsOfK, ← hc]
  congr 1
  apply (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
  exact C.i_cyclesMk _ _ _ _

/-- **Naturality of the class of a cocycle.** -/
theorem homologyMap_clsOfK (φ : C ⟶ D) (n : ℕ) (z : C.X n)
    (hz : (C.d n (n + 1)).hom z = 0)
    (hz' : (D.d n (n + 1)).hom ((φ.f n).hom z) = 0) :
    (HomologicalComplex.homologyMap φ n).hom (clsOfK C n z hz)
      = clsOfK D n ((φ.f n).hom z) hz' := by
  rw [clsOfK, ← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    ModuleCat.comp_apply, clsOfK]
  apply congrArg (D.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).1 inferInstance
  calc
    _ = ((C.iCycles n ≫ φ.f n).hom)
          (C.cyclesMk z (n + 1) (ComplexShape.next_eq' _ (upRel n)) hz) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ n) _
    _ = (φ.f n).hom z := by
      rw [ModuleCat.comp_apply]
      exact congrArg (φ.f n).hom (C.i_cyclesMk _ _ _ _)
    _ = _ := (D.i_cyclesMk _ _ _ _).symm

/-- A cochain map preserves cocycles. -/
theorem d_map_eq_zeroK (φ : C ⟶ D) (n : ℕ) (z : C.X n)
    (hz : (C.d n (n + 1)).hom z = 0) :
    (D.d n (n + 1)).hom ((φ.f n).hom z) = 0 := by
  have hcomm := φ.comm n (n + 1)
  rw [← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply, hz, map_zero]

end CohClass

namespace MVDelta

variable {X : TopCat.{0}}

/-- The class in `H^p(X₃)` of a cocycle of the third term. -/
def cls₃Of (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (x₃ : (mvCoSCOf K U V hUV).X₃.X p)
    (hx₃ : ((mvCoSCOf K U V hUV).X₃.d p (p + 1)).hom x₃ = 0) :
    (mvCoSCOf K U V hUV).X₃.homology p :=
  ((mvCoSCOf K U V hUV).X₃.homologyπ p).hom
    ((mvCoSCOf K U V hUV).X₃.cyclesMk x₃ (p + 1) (ComplexShape.next_eq' _ (upRel p)) hx₃)

/-- The class in `H^{p+1}(X₁)` of a cocycle of the first term. -/
def cls₁Of (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (x₁ : (mvCoSCOf K U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSCOf K U V hUV).X₁.d (p + 1) (p + 2)).hom x₁ = 0) :
    (mvCoSCOf K U V hUV).X₁.homology (p + 1) :=
  ((mvCoSCOf K U V hUV).X₁.homologyπ (p + 1)).hom
    ((mvCoSCOf K U V hUV).X₁.cyclesMk x₁ (p + 2)
      (ComplexShape.next_eq' _ (upRel (p + 1))) hx₁)

/-- **A descended element is a cocycle.** -/
theorem d_eq_zero_of_descendsOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (p : ℕ) (x₂ : (mvCoSCOf K U V hUV).X₂.X p) (x₁ : (mvCoSCOf K U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSCOf K U V hUV).f.f (p + 1)).hom x₁
      = ((mvCoSCOf K U V hUV).X₂.d p (p + 1)).hom x₂) :
    ((mvCoSCOf K U V hUV).X₁.d (p + 1) (p + 2)).hom x₁ = 0 :=
  (mvCoSCOf_shortExact K U V hUV).d_eq_zero_of_f_eq_d_apply p (p + 1) x₂ x₁ hx₁ (p + 2)

/-- **The connecting map from a lift**, over any coefficient ring. -/
theorem delta_applyOf (K : Type) [CommRing K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (p : ℕ)
    (x₃ : (mvCoSCOf K U V hUV).X₃.X p)
    (hx₃ : ((mvCoSCOf K U V hUV).X₃.d p (p + 1)).hom x₃ = 0)
    (x₂ : (mvCoSCOf K U V hUV).X₂.X p)
    (hx₂ : ((mvCoSCOf K U V hUV).g.f p).hom x₂ = x₃)
    (x₁ : (mvCoSCOf K U V hUV).X₁.X (p + 1))
    (hx₁ : ((mvCoSCOf K U V hUV).f.f (p + 1)).hom x₁
      = ((mvCoSCOf K U V hUV).X₂.d p (p + 1)).hom x₂) :
    ((mvCoSCOf_shortExact K U V hUV).δ p (p + 1) (upRel p)).hom (cls₃Of K U V hUV p x₃ hx₃)
      = cls₁Of K U V hUV p x₁ (d_eq_zero_of_descendsOf K U V hUV p x₂ x₁ hx₁) :=
  (mvCoSCOf_shortExact K U V hUV).δ_apply p (p + 1) (upRel p) x₃ hx₃ x₂ hx₂ x₁ hx₁ (p + 2)
    (ComplexShape.next_eq' _ (upRel (p + 1)))

end MVDelta

end

end GroupApproximation.CharClass
