import GroupApproximation.CharClass.MayerVietorisElementOf

/-!
# The left end of Mayer–Vietoris over a field

The coefficient-generic form of `MayerVietorisZero`: a degree-zero class of the ambient
space that restricts to zero on both pieces of the cover is zero.  The reason is the same
at every coefficient ring: in a cochain complex indexed by `ℕ` there are no coboundaries
into degree zero, so `H⁰ = Z⁰`, and the Mayer–Vietoris map is a degreewise monomorphism
because the dualized sequence is degreewise split short exact.

## Main results

* `mono_homologyMap_zeroOf` — a degreewise mono of cochain complexes of `K`-modules over
  `ℕ` is mono on `H⁰`.
* `mvExactZeroOf`, `mvResPairOf_injective` — the left end.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **A degreewise monomorphism of cochain complexes is a monomorphism on `H⁰`**, over
any coefficient ring. -/
theorem mono_homologyMap_zeroOf {R : Type} [CommRing R]
    {C D : CochainComplex (ModuleCat.{0} R) ℕ} (φ : C ⟶ D) [Mono (φ.f 0)] :
    Mono (HomologicalComplex.homologyMap φ 0) := by
  haveI hcyc : Mono (HomologicalComplex.cyclesMap φ 0) := by
    haveI : Mono (HomologicalComplex.cyclesMap φ 0 ≫ D.iCycles 0) := by
      rw [HomologicalComplex.cyclesMap_i]
      infer_instance
    exact mono_of_mono _ (D.iCycles 0)
  haveI : Mono (C.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  have hfac : HomologicalComplex.homologyMap φ 0
      = inv (C.homologyπ 0) ≫ (C.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0) := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac]
  infer_instance

/-- **Exactness at the left end of Mayer–Vietoris, over a field.** -/
theorem mvExactZeroOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    {x : Hmod K X 0} (hU : (mvResUOf K U V hUV 0).hom x = 0)
    (hV : (mvResVOf K U V hUV 0).hom x = 0) : x = 0 := by
  haveI : Mono ((mvCoSCOf K U V hUV).f.f 0) :=
    (mvCoSCOf_degreewise_shortExact K U V hUV 0).mono_f
  haveI := mono_homologyMap_zeroOf (mvCoSCOf K U V hUV).f
  have h1 : (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f 0).hom
      ((mvAmbientIsoOf K U V hUV 0).inv.hom x) = 0 :=
    (mvPhiOf_eq_zero_iff K U V hUV 0 x).2 ⟨hU, hV⟩
  have h2 : (mvAmbientIsoOf K U V hUV 0).inv.hom x = 0 := by
    have hinj := (ModuleCat.mono_iff_injective
      (HomologicalComplex.homologyMap (mvCoSCOf K U V hUV).f 0)).1 inferInstance
    apply hinj
    rw [h1, map_zero]
  exact eq_zero_of_iso_hom_eq_zeroOf (mvAmbientIsoOf K U V hUV 0).symm h2

/-- The same, as injectivity of the pair of restrictions. -/
theorem mvResPairOf_injective (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    {x y : Hmod K X 0} (hU : (mvResUOf K U V hUV 0).hom x = (mvResUOf K U V hUV 0).hom y)
    (hV : (mvResVOf K U V hUV 0).hom x = (mvResVOf K U V hUV 0).hom y) : x = y := by
  have h : x - y = 0 := by
    refine mvExactZeroOf K U V hUV ?_ ?_
    · rw [map_sub, hU, sub_self]
    · rw [map_sub, hV, sub_self]
  exact sub_eq_zero.1 h

end

end GroupApproximation.CharClass
