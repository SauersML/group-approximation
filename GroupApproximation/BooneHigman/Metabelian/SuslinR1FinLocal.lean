import GroupApproximation.BooneHigman.Metabelian.SuslinR1Statement
import GroupApproximation.BooneHigman.Metabelian.SuslinR1Columns
import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksRow
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalQuillen
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseLift
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicKaroubi
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import GroupApproximation.Meta.AxiomGuard

/-!
# R1, finite form: a unit leading coefficient gives an elementary matrix, given R2

Lane `bh-met-90r`.  Let `ρ ∈ SL_N(A[X])` (not necessarily normalized), `N ≥ 3`, with
`SL_N(A) ⊆ E_N(A)` and R2 (`SuslinR1StabLocal A N`).  If for some `ε ∈ E_N(A[X])` an entry of
`ρ ε` has a UNIT leading coefficient, then `ρ ∈ E_N(A[X])` (`suslinR1Fin_mem_of_unit_lead`).

Proof.  Put `w = C(ρ(0)) ∈ E_N(A[X])` (because `ρ(0) ∈ SL_N(A) ⊆ E_N(A)`) and `σ = ρ w⁻¹`, which
is normalized with determinant `1`, and `σ (w ε) = ρ ε`.  At a maximal ideal `𝔪`, with
`B = A_𝔪`: if `u` is the leading coefficient of the entry `(r, t)`, then `C(u⁻¹)` times that
entry is monic, and it lies in the ideal of the entries of row `r` outside any other column
`t'`.  `suslinR1_monic_of_mem_span` makes the entry at `(r, t')` monic, local Horrocks
(`suslinHorrocks_row`) makes row `r` equal to `e_r`, and R2 gives `σ_𝔪 ∈ E_N(B[X])`.  Clearing
denominators (`suslinLocalCase_away_of_loc`), the dilation step (`suslinDilAn_quillen_of_map`)
and Quillen patching (`suslinLocalGlobal_mem_elementaryGroup`) give `σ ∈ E_N(A[X])`, so
`ρ = σ w ∈ E_N(A[X])`.  No change of variables is used here; that is the input of
`SuslinR1FinCoord.lean`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Over a local ring, if `C(b)` times the entry `(r, t)` of `M` is monic, then an elementary
`F` makes row `r` of `M F` equal to `e_r`. -/
theorem suslinR1Fin_row_of_unit_lead {B : Type*} [CommRing B] [IsLocalRing B] {N : ℕ}
    (hN : 3 ≤ N) (M : Matrix.GeneralLinearGroup (Fin N) (Polynomial B)) (r t : Fin N) (b : B)
    (hmon : (Polynomial.C b * (M : Matrix (Fin N) (Fin N) (Polynomial B)) r t).Monic) :
    ∃ F ∈ elementaryGroup (Fin N) (Polynomial B),
      ∀ c : Fin N, ((M * F : Matrix.GeneralLinearGroup (Fin N) (Polynomial B)) :
        Matrix (Fin N) (Fin N) (Polynomial B)) r c = if c = r then 1 else 0 := by
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨t', ht'⟩ := exists_ne t
  have hmem : Polynomial.C b * (M : Matrix (Fin N) (Fin N) (Polynomial B)) r t ∈
      Ideal.span (Set.range fun j : {j : Fin N // j ≠ t'} ↦
        (M : Matrix (Fin N) (Fin N) (Polynomial B)) r j) :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨t, ht'.symm⟩, rfl⟩)
  obtain ⟨F1, hF1, hF1m⟩ := suslinR1_monic_of_mem_span M r t' hmon hmem
  obtain ⟨F2, hF2, hrow⟩ :=
    suslinHorrocks_row (by rw [Fintype.card_fin]; exact hN) (M * F1) r t' hF1m
  refine ⟨F1 * F2, mul_mem hF1 hF2, fun c ↦ ?_⟩
  rw [← mul_assoc]
  exact hrow c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_row_of_unit_lead

/-- **The local step.**  For normalized `σ ∈ SL_N(A[X])`, if an entry of `σ G`, with `G`
elementary, has a unit leading coefficient, then R2 makes `σ_𝔪` elementary at every maximal
`𝔪`. -/
theorem suslinR1Fin_loc_of_unit_lead {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (h2 : SuslinR1StabLocal A N) (σ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hσ : Matrix.det (σ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1)
    (hσ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) σ = 1)
    (G : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hG : G ∈ elementaryGroup (Fin N) (Polynomial A)) (r t : Fin N)
    (hu : IsUnit (((σ * G : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
      Matrix (Fin N) (Fin N) (Polynomial A)) r t).leadingCoeff)
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ ∈
      elementaryGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪)) := by
  have hmon : (Polynomial.C (algebraMap A (Localization.AtPrime 𝔪) (hu.unit⁻¹ : Aˣ)) *
      ((elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) (σ * G) :
          Matrix.GeneralLinearGroup (Fin N) (Polynomial (Localization.AtPrime 𝔪))) :
        Matrix (Fin N) (Fin N) (Polynomial (Localization.AtPrime 𝔪))) r t).Monic := by
    have h := (Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one hu.val_inv_mul).map
      (algebraMap A (Localization.AtPrime 𝔪))
    rw [Polynomial.map_mul, Polynomial.map_C] at h
    exact h
  obtain ⟨F, hF, hrow⟩ := suslinR1Fin_row_of_unit_lead hN _ r t _ hmon
  refine h2 σ hσ hσ0 𝔪 h𝔪 (elementaryMatrixUnitMap (ι := Fin N)
    (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) G * F)
    (mul_mem (elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ hG)) hF)
    r fun c ↦ ?_
  rw [← mul_assoc, ← map_mul]
  exact hrow c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_loc_of_unit_lead

/-- **A unit leading coefficient gives an elementary matrix, given R2.**  For `N ≥ 3`, with
`SL_N(A) ⊆ E_N(A)` and R2, if some entry of `ρ ε` (`ρ ∈ SL_N(A[X])`, `ε ∈ E_N(A[X])`) has a unit
leading coefficient, then `ρ ∈ E_N(A[X])`. -/
theorem suslinR1Fin_mem_of_unit_lead {A : Type*} [CommRing A] {N : ℕ} (hN : 3 ≤ N)
    (hA : SpecialLinearInElementary A N) (h2 : SuslinR1StabLocal A N)
    (ρ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hρ : Matrix.det (ρ : Matrix (Fin N) (Fin N) (Polynomial A)) = 1)
    (ε : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hε : ε ∈ elementaryGroup (Fin N) (Polynomial A)) (r t : Fin N)
    (hu : IsUnit (((ρ * ε : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
      Matrix (Fin N) (Fin N) (Polynomial A)) r t).leadingCoeff) :
    ρ ∈ elementaryGroup (Fin N) (Polynomial A) := by
  obtain ⟨w, hwdef⟩ : ∃ w : Matrix.GeneralLinearGroup (Fin N) (Polynomial A),
      w = elementaryMatrixUnitMap (ι := Fin N) (Polynomial.C (R := A))
        (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) ρ) :=
    ⟨_, rfl⟩
  have hv : Matrix.det ((elementaryMatrixUnitMap (ι := Fin N)
      (Polynomial.constantCoeff (R := A)) ρ : Matrix.GeneralLinearGroup (Fin N) A) :
        Matrix (Fin N) (Fin N) A) = 1 := by
    change Matrix.det ((Polynomial.constantCoeff (R := A)).mapMatrix
      (ρ : Matrix (Fin N) (Fin N) (Polynomial A))) = 1
    rw [← RingHom.map_det, hρ, map_one]
  have hw : w ∈ elementaryGroup (Fin N) (Polynomial A) := by
    rw [hwdef]
    exact elementaryGroup_map_le (ι := Fin N) (Polynomial.C (R := A))
      (Subgroup.mem_map_of_mem _ (hA _ hv))
  have hww : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) w =
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A)) ρ := by
    rw [hwdef]
    exact suslinMonic_constantCoeff_map_C _
  have hσ : Matrix.det ((ρ * w⁻¹ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
      Matrix (Fin N) (Fin N) (Polynomial A)) = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hρ,
      suslin_det_eq_one_of_mem_elementaryGroup (inv_mem hw), one_mul]
  have hσ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := A))
      (ρ * w⁻¹) = 1 := by
    rw [map_mul, map_inv, hww]
    exact mul_inv_cancel _
  have hu' : IsUnit (((ρ * w⁻¹ * (w * ε) : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) :
      Matrix (Fin N) (Fin N) (Polynomial A)) r t).leadingCoeff := by
    rwa [mul_assoc, inv_mul_cancel_left]
  have hmem : ρ * w⁻¹ ∈ elementaryGroup (Fin N) (Polynomial A) :=
    suslinLocalGlobal_mem_elementaryGroup _ hσ0 fun 𝔪 h𝔪 ↦ by
      obtain ⟨a, ha, hloc⟩ := suslinLocalCase_away_of_loc (Localization.AtPrime 𝔪)
        𝔪.primeCompl _ (suslinR1Fin_loc_of_unit_lead hN h2 _ hσ hσ0 _ (mul_mem hw hε) r t hu'
          𝔪 h𝔪)
      obtain ⟨k, hk⟩ := suslinDilAn_quillen_of_map (by omega)
        (algebraMap A (Localization.Away a)) a (suslinDilAn_away_surj a)
        (suslinDilAn_away_ker a) _ hloc
      exact ⟨a ^ k, fun hk𝔪 ↦ Ideal.mem_primeCompl_iff.1 ha (h𝔪.isPrime.mem_of_pow_mem k hk𝔪),
        hk⟩
  have hρw := mul_mem hmem hw
  rwa [inv_mul_cancel_right] at hρw

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Fin_mem_of_unit_lead

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
