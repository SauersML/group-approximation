import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatchFin
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalCompose
import GroupApproximation.Meta.AxiomGuard

/-!
# Local-global plumbing for monic inversion

Lane `bh-sus-02`.  Unconditional ring-hom bookkeeping used to reduce monic inversion to local
rings:

* `suslinLG_localGlobal`: the Quillen–Suslin local-global principle for `E_N`, `N > 2`, in the
  normalized form `σ(0) = 1` (a thin wrapper of `suslinMonicPatch_localGlobal_fin`);
* `suslinLG_zero_map`: the normalization `σ(0) = 1` survives any base change `A → R`;
* `suslinLG_awayMap`: the induced map `A[X]_f → R[X]_{f_R}` and its compatibility
  `suslinLG_awayMap_comp`;
* `suslinLG_away_mem_map`: `f`-local elementarity survives base change.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A] {N : ℕ}

/-- **Quillen–Suslin local-global principle for `E_N`, `N > 2`** (normalized form): if
`σ ∈ GL_N(A[X])`, `σ(0) = 1` and `σ_𝔪 ∈ E_N(A_𝔪[X])` for every maximal `𝔪`, then
`σ ∈ E_N(A[X])`. -/
theorem suslinLG_localGlobal (hN : 2 < N)
    (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (h0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) σ = 1)
    (hloc : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∈
        elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))) :
    σ ∈ elementaryGroup (Fin N) (Polynomial A) := by
  refine suslinMonicPatch_localGlobal_fin hN σ ?_ hloc
  rw [h0]
  exact one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_localGlobal

/-- `constantCoeff ∘ map g = g ∘ constantCoeff`. -/
theorem suslinLG_constantCoeff_comp_map {R : Type*} [CommRing R] (g : A →+* R) :
    (Polynomial.constantCoeff (R := R)).comp (Polynomial.mapRingHom g) =
      g.comp (Polynomial.constantCoeff (R := A)) :=
  RingHom.ext fun p ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.constantCoeff_apply,
      Polynomial.constantCoeff_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_constantCoeff_comp_map

/-- The normalization `σ(0) = 1` is preserved by base change along `g : A →+* R`. -/
theorem suslinLG_zero_map {R : Type*} [CommRing R] (g : A →+* R)
    (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (h0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) σ = 1) :
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := R))
        (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom g) σ) = 1 := by
  rw [suslinLocalGlobal_map_map, suslinLG_constantCoeff_comp_map,
    ← suslinLocalGlobal_map_map, h0, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_zero_map

/-- The induced map `A[X]_f → R[X]_{g(f)}` of a base change `g : A →+* R`. -/
noncomputable def suslinLG_awayMap {R : Type*} [CommRing R] (g : A →+* R)
    (f : Polynomial A) :
    Localization.Away f →+* Localization.Away (Polynomial.mapRingHom g f) :=
  IsLocalization.Away.map (Localization.Away f)
    (Localization.Away (Polynomial.mapRingHom g f)) (Polynomial.mapRingHom g) f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_awayMap

/-- Compatibility of `suslinLG_awayMap` with the localization maps. -/
theorem suslinLG_awayMap_comp {R : Type*} [CommRing R] (g : A →+* R) (f : Polynomial A) :
    (suslinLG_awayMap g f).comp (algebraMap (Polynomial A) (Localization.Away f)) =
      (algebraMap (Polynomial R) (Localization.Away (Polynomial.mapRingHom g f))).comp
        (Polynomial.mapRingHom g) := by
  unfold suslinLG_awayMap IsLocalization.Away.map
  exact IsLocalization.map_comp _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_awayMap_comp

/-- `f`-local elementarity is preserved by base change along `g : A →+* R`. -/
theorem suslinLG_away_mem_map {R : Type*} [CommRing R] (g : A →+* R) (f : Polynomial A)
    (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hσ : elementaryMatrixUnitMap (ι := Fin N)
        (algebraMap (Polynomial A) (Localization.Away f)) σ ∈
      elementaryGroup (Fin N) (Localization.Away f)) :
    elementaryMatrixUnitMap (ι := Fin N)
        (algebraMap (Polynomial R) (Localization.Away (Polynomial.mapRingHom g f)))
        (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom g) σ) ∈
      elementaryGroup (Fin N) (Localization.Away (Polynomial.mapRingHom g f)) := by
  rw [suslinLocalGlobal_map_map, ← suslinLG_awayMap_comp, ← suslinLocalGlobal_map_map]
  exact elementaryGroup_map_le _ (Subgroup.mem_map_of_mem _ hσ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLG_away_mem_map

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
