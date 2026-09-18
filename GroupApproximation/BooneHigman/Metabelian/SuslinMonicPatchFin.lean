import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseLift
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalQuillen
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin's local-global principle for `E_N`, `N ≥ 3`, in `Fin N` form

Lane `bh-met-93n`.  For any commutative ring `A`, `N > 2` and `τ ∈ GL_N(A[X])`:
if `τ(0) ∈ E_N(A)` and the image of `τ` lies in `E_N(A_𝔪[X])` for every maximal ideal `𝔪`,
then `τ ∈ E_N(A[X])` (`suslinMonicPatch_localGlobal_fin`).

The proof only composes corpus lemmas that are already unconditional:

* normalize: `σ = τ · C(τ(0))⁻¹` has `σ(0) = 1` (`suslinMonicPatch_normalize_zero`);
* `σ` is still locally elementary, since `C(τ(0)) ∈ E_N(A[X])`;
* clear denominators, `A_𝔪 ⇝ A_a` with `a ∉ 𝔪` (`suslinLocalCase_away_of_loc`);
* the dilation lemma gives `a ^ k ∈ Q(σ)` (`suslinDilAn_quillen_of_map`);
* Quillen's ideal argument gives `σ ∈ E_N(A[X])` (`suslinLocalGlobal_mem_elementaryGroup`);
* `τ = σ · C(τ(0))`.

No patching hypothesis, no citation, no `K₂` or homotopy-invariance input.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A] {N : ℕ}

/-- `constantCoeff ∘ C = id`. -/
theorem suslinMonicPatch_constantCoeff_comp_C :
    (Polynomial.constantCoeff (R := A)).comp (Polynomial.C : A →+* Polynomial A) =
      RingHom.id A :=
  RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero,
      RingHom.id_apply]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_constantCoeff_comp_C

/-- The constant matrix `C(τ(0)) ∈ GL_N(A[X])`. -/
noncomputable def suslinMonicPatch_const
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
    Matrix.GeneralLinearGroup (Fin N) (Polynomial A) :=
  elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C : A →+* Polynomial A)
    (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_const

/-- If `τ(0) ∈ E_N(A)` then `C(τ(0)) ∈ E_N(A[X])`. -/
theorem suslinMonicPatch_const_mem (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (h0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ ∈
      elementaryGroup (Fin N) A) :
    suslinMonicPatch_const τ ∈ elementaryGroup (Fin N) (Polynomial A) :=
  elementaryGroup_map_le (ι := Fin N) (Polynomial.C : A →+* Polynomial A)
    (Subgroup.mem_map_of_mem _ h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_const_mem

/-- The normalized matrix `τ · C(τ(0))⁻¹` has constant term `1`. -/
theorem suslinMonicPatch_normalize_zero
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
    elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A))
      (τ * (suslinMonicPatch_const τ)⁻¹) = 1 := by
  unfold suslinMonicPatch_const
  rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinMonicPatch_constantCoeff_comp_C,
    suslinLocalGlobal_map_id, mul_inv_cancel]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_normalize_zero

/-- **Suslin's local-global principle for `E_N`, `N > 2`**, over every commutative ring.
Unconditional: the Quillen ideal of the normalized matrix meets the complement of every
maximal ideal, by clearing denominators and the dilation lemma. -/
theorem suslinMonicPatch_localGlobal_fin (hN : 2 < N)
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (h0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) τ ∈
      elementaryGroup (Fin N) A)
    (hloc : ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
      elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ ∈
        elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))) :
    τ ∈ elementaryGroup (Fin N) (Polynomial A) := by
  have hc := suslinMonicPatch_const_mem τ h0
  have hσ : τ * (suslinMonicPatch_const τ)⁻¹ ∈ elementaryGroup (Fin N) (Polynomial A) := by
    refine suslinLocalGlobal_mem_elementaryGroup _ (suslinMonicPatch_normalize_zero τ) ?_
    intro 𝔪 h𝔪
    have hm : elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
          (τ * (suslinMonicPatch_const τ)⁻¹) ∈
        elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)) := by
      rw [map_mul, map_inv]
      exact mul_mem (hloc 𝔪 h𝔪) (inv_mem (elementaryGroup_map_le (ι := Fin N)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪)))
        (Subgroup.mem_map_of_mem _ hc)))
    obtain ⟨a, ha, hmem⟩ :=
      suslinLocalCase_away_of_loc (Localization.AtPrime 𝔪) 𝔪.primeCompl _ hm
    obtain ⟨k, hk⟩ := suslinDilAn_quillen_of_map hN (algebraMap A (Localization.Away a)) a
      (suslinDilAn_away_surj a) (suslinDilAn_away_ker a) _ hmem
    exact ⟨a ^ k, fun hk𝔪 ↦ Ideal.mem_primeCompl_iff.1 ha (h𝔪.isPrime.mem_of_pow_mem k hk𝔪),
      hk⟩
  have h := mul_mem hσ hc
  rwa [inv_mul_cancel_right] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicPatch_localGlobal_fin

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
