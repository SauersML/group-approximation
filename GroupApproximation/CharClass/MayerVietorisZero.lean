import GroupApproximation.CharClass.MayerVietorisElement

/-!
# The left end of Mayer–Vietoris: the pair of restrictions is injective in degree zero

The Mayer–Vietoris sequence begins

```text
0 → H⁰(X) → H⁰(U) ⊕ H⁰(V) → H⁰(U ∩ V) → H¹(X) → ⋯
```

and `MayerVietorisElement.lean` supplies exactness at every spot except the left end,
which is not an instance of `mvExactX` (there is no degree below zero for the connecting
map to come from).  This file supplies it.

The reason it is true has nothing to do with the cover.  In a cochain complex indexed by
`ℕ` there are no coboundaries into degree zero, so `H⁰ = Z⁰` — Mathlib's
`CochainComplex.isIso_homologyπ₀` — and a degreewise monomorphism of such complexes is
therefore injective on `H⁰`.  The Mayer–Vietoris map `f` is a degreewise monomorphism
because the dualized sequence is degreewise split short exact.

## Main results

* `mono_homologyMap_zero` — a degreewise mono of cochain complexes over `ℕ` is mono on
  `H⁰`.
* `mvExactZero` — a class of `H⁰(X)` restricting to zero on both pieces is zero.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **A degreewise monomorphism of cochain complexes is a monomorphism on `H⁰`.**
There are no coboundaries into degree zero, so `H⁰` is the cycles and the map on `H⁰` is
the restriction of the degree-zero component. -/
theorem mono_homologyMap_zero {K L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (φ : K ⟶ L) [Mono (φ.f 0)] : Mono (HomologicalComplex.homologyMap φ 0) := by
  haveI hcyc : Mono (HomologicalComplex.cyclesMap φ 0) := by
    haveI : Mono (HomologicalComplex.cyclesMap φ 0 ≫ L.iCycles 0) := by
      rw [HomologicalComplex.cyclesMap_i]
      infer_instance
    exact mono_of_mono _ (L.iCycles 0)
  haveI : Mono (K.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0) := by
    rw [HomologicalComplex.homologyπ_naturality]
    infer_instance
  have hfac : HomologicalComplex.homologyMap φ 0
      = inv (K.homologyπ 0) ≫ (K.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0) := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac]
  infer_instance

/-- **Exactness at the left end of Mayer–Vietoris.**  A degree-zero class of the ambient
space restricting to zero on both pieces of the cover is zero. -/
theorem mvExactZero (U V : Opens X) (hUV : U ⊔ V = ⊤) {x : Hmod2 X 0}
    (hU : (mvResU U V hUV 0).hom x = 0) (hV : (mvResV U V hUV 0).hom x = 0) : x = 0 := by
  haveI : Mono ((mvCoSC U V hUV).f.f 0) := (mvCoSC_degreewise_shortExact U V hUV 0).mono_f
  haveI := mono_homologyMap_zero (mvCoSC U V hUV).f
  have h1 : (HomologicalComplex.homologyMap (mvCoSC U V hUV).f 0).hom
      ((mvAmbientIso U V hUV 0).inv.hom x) = 0 :=
    (mvPhi_eq_zero_iff U V hUV 0 x).2 ⟨hU, hV⟩
  have h2 : (mvAmbientIso U V hUV 0).inv.hom x = 0 := by
    have hinj := (ModuleCat.mono_iff_injective
      (HomologicalComplex.homologyMap (mvCoSC U V hUV).f 0)).1 inferInstance
    apply hinj
    rw [h1, map_zero]
  exact eq_zero_of_iso_hom_eq_zero (mvAmbientIso U V hUV 0).symm h2

/-- The same, as injectivity of the pair of restrictions. -/
theorem mvResPair_injective (U V : Opens X) (hUV : U ⊔ V = ⊤) {x y : Hmod2 X 0}
    (hU : (mvResU U V hUV 0).hom x = (mvResU U V hUV 0).hom y)
    (hV : (mvResV U V hUV 0).hom x = (mvResV U V hUV 0).hom y) : x = y := by
  have h : x - y = 0 := by
    refine mvExactZero U V hUV ?_ ?_
    · rw [map_sub, hU, sub_self]
    · rw [map_sub, hV, sub_self]
  exact sub_eq_zero.1 h

end

end GroupApproximation.CharClass
