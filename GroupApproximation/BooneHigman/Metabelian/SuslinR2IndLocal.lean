import GroupApproximation.BooneHigman.Metabelian.SuslinR2IndLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank induction for R2, part 3: normalized local matrices from the local case

Lane `bh-met-90q`.  `suslinR2Ind_mem_of_localCase`: if `A → A_𝔪` is injective, the local case
at rank `n` makes every `σ ∈ SL_n(A_𝔪[X])` with `σ(0) = 1` elementary.  The proof is
sketched in `SuslinR2IndLift.lean`: common denominator `s ∉ 𝔪`, dilation lift to `A[X]`, the
local case, and undoing the dilation.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **Normalized local matrices are elementary**, given the local case at the same rank and
injectivity of `A → A_𝔪`. -/
theorem suslinR2Ind_mem_of_localCase {A : Type*} [CommRing A] {n : ℕ}
    (hL : SuslinLocalCaseStatement A n) (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal)
    (hf : Function.Injective (algebraMap A (Localization.AtPrime 𝔪)))
    (σ : (Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X])ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) = 1)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := Localization.AtPrime 𝔪)) σ =
      1) :
    σ ∈ elementaryGroup (Fin n) (Localization.AtPrime 𝔪)[X] := by
  obtain ⟨s, hs, q, hq⟩ := suslinR2Ind_common_denom 𝔪.primeCompl
    (Sum.elim
      (fun ij : Fin n × Fin n ↦
        (σ : Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) ij.1 ij.2)
      (fun ij : Fin n × Fin n ↦
        ((σ⁻¹ : (Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X])ˣ) :
          Matrix (Fin n) (Fin n) (Localization.AtPrime 𝔪)[X]) ij.1 ij.2))
  have h0i : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := Localization.AtPrime 𝔪))
      σ⁻¹ = 1 := by
    rw [map_inv, h0, inv_one]
  obtain ⟨P, hP, hP0⟩ := suslinR2Ind_lift_matrix (algebraMap A (Localization.AtPrime 𝔪)) σ h0
    s (fun i j ↦ q (Sum.inl (i, j))) (fun i j ↦ hq (Sum.inl (i, j)))
  obtain ⟨Q, hQ, -⟩ := suslinR2Ind_lift_matrix (algebraMap A (Localization.AtPrime 𝔪)) σ⁻¹ h0i
    s (fun i j ↦ q (Sum.inr (i, j))) (fun i j ↦ hq (Sum.inr (i, j)))
  have hPQ : P * Q = 1 := suslinR2Ind_mapMatrix_injective hf _ _ (by
    rw [map_mul, hP, hQ, ← map_mul, Units.mul_inv, map_one, map_one])
  have hQP : Q * P = 1 := suslinR2Ind_mapMatrix_injective hf _ _ (by
    rw [map_mul, hP, hQ, ← map_mul, Units.inv_mul, map_one, map_one])
  let τ' : (Matrix (Fin n) (Fin n) A[X])ˣ := ⟨P, Q, hPQ, hQP⟩
  have hdet' : Matrix.det (τ' : Matrix (Fin n) (Fin n) A[X]) = 1 := by
    apply Polynomial.map_injective (algebraMap A (Localization.AtPrime 𝔪)) hf
    change mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) (Matrix.det P) =
      mapRingHom (algebraMap A (Localization.AtPrime 𝔪)) 1
    rw [RingHom.map_det, hP, ← RingHom.map_det, hdet, map_one, map_one]
  have hτ0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) τ' = 1 := by
    apply Units.ext
    ext i j
    change Polynomial.constantCoeff (P i j) = (1 : Matrix (Fin n) (Fin n) A) i j
    rw [Polynomial.constantCoeff_apply, hP0]
  have hmem := hL τ' hdet' hτ0 𝔪 h𝔪
  have heq : elementaryMatrixUnitMap (ι := Fin n)
      (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) τ' =
      elementaryMatrixUnitMap (compRingHom (C (algebraMap A (Localization.AtPrime 𝔪) s) * X))
        σ :=
    Units.ext hP
  rw [heq] at hmem
  obtain ⟨c, hc⟩ :=
    (IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨s, hs⟩ : 𝔪.primeCompl)).exists_right_inv
  exact suslinR2Ind_mem_of_dilate hc σ hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_mem_of_localCase

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
