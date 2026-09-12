import GroupApproximation.Algebra.ValuationWithTopInt
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# The places of a finite separable extension over a discrete place

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`, tex lines 1146--1147).

Let `w : L → ℤᵐ⁰` be a valuation with a uniformizer (`w π = exp (-1)`) and `K / L` a finite
separable extension.  The valuation ring `O` of `w` is a principal ideal domain, so its integral
closure `C` in `K` is a Dedekind domain, and every height-one prime of `C` lies over the maximal
ideal of `O`; there are finitely many.  Their valuations `u_1, …, u_r` on `K`
(`exists_places_over`) satisfy

* each `u_j` has a uniformizer;
* `u_j π < 1`;
* if `u_j x ≤ 1` for all `j`, then `x ∈ C`, so the minimal polynomial of `x` over `L` has all
  coefficients in `O`.
-/

namespace GroupApproximation
namespace ValuationExtension

open WithZero IsDedekindDomain

variable {L : Type*} [Field L] (w : Valuation L ℤᵐ⁰)

/-- The valuation ring of a `ℤᵐ⁰`-valued valuation is a principal ideal ring. -/
theorem isPrincipalIdealRing_valuationSubring : IsPrincipalIdealRing w.valuationSubring := by
  rw [(Valuation.valuationSubring.integers w).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using w.toMonoidWithZeroHom.range_nontrivial

variable (K : Type*) [Field K] [Algebra L K] [FiniteDimensional L K] [Algebra.IsSeparable L K]

/-- **The places over a discrete place.** -/
theorem exists_places_over {π : L} (hπ : w π = exp (-1 : ℤ)) :
    ∃ (r : ℕ) (u : Fin r → Valuation K ℤᵐ⁰),
      (∀ j, ∃ ϖ : K, u j ϖ = exp (-1 : ℤ)) ∧
      (∀ j, u j (algebraMap L K π) < 1) ∧
      ∀ x : K, (∀ j, u j x ≤ 1) → ∀ i, w ((minpoly L x).coeff i) ≤ 1 := by
  classical
  let O := w.valuationSubring
  haveI : IsPrincipalIdealRing O := isPrincipalIdealRing_valuationSubring w
  letI : Algebra O K := ((algebraMap L K).comp (algebraMap O L)).toAlgebra
  haveI : IsScalarTower O L K := IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure O K
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain (A := O) (K := L) (L := K)
  haveI : IsFractionRing C K :=
    integralClosure.isFractionRing_of_finite_extension (A := O) (K := L) (L := K)
  have hunder : ∀ P : HeightOneSpectrum C,
      P.asIdeal.under O = IsLocalRing.maximalIdeal O := fun P ↦
    IsLocalRing.eq_maximalIdeal (HeightOneSpectrum.under O P).isMaximal
  have hπO : π ∈ O := by
    show w π ≤ 1
    rw [hπ, ← exp_zero, exp_le_exp]
    norm_num
  have hmax : (⟨π, hπO⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]
    show w π < 1
    rw [hπ, ← exp_zero, exp_lt_exp]
    norm_num
  have hmem : ∀ P : HeightOneSpectrum C, algebraMap O C ⟨π, hπO⟩ ∈ P.asIdeal := by
    intro P
    have h := hmax
    rw [← hunder P] at h
    exact h
  have hπK : algebraMap C K (algebraMap O C ⟨π, hπO⟩) = algebraMap L K π := rfl
  have hπC : algebraMap O C ⟨π, hπO⟩ ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap C K) h
    rw [hπK, map_zero] at h'
    have hπ0 : π ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hπ
      exact exp_ne_zero hπ.symm
    exact hπ0 ((FaithfulSMul.algebraMap_injective L K) (h'.trans (map_zero _).symm))
  haveI hfin : Finite (HeightOneSpectrum C) := by
    have hI : Ideal.span {algebraMap O C ⟨π, hπO⟩} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hπC
    refine Set.finite_univ_iff.mp ((Ideal.finite_factors hI).subset fun P _ ↦ ?_)
    show P.asIdeal ∣ Ideal.span {algebraMap O C ⟨π, hπO⟩}
    rw [Ideal.dvd_span_singleton]
    exact hmem P
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (HeightOneSpectrum C)
  refine ⟨r, fun j ↦ (e.symm j).valuation K, fun j ↦ (e.symm j).valuation_exists_uniformizer K,
    fun j ↦ ?_, fun x hx i ↦ ?_⟩
  · have h := ((e.symm j).valuation_lt_one_iff_mem (K := K) (algebraMap O C ⟨π, hπO⟩)).mpr
      (hmem (e.symm j))
    exact h
  · have hall : ∀ P : HeightOneSpectrum C, P.valuation K x ≤ 1 := fun P ↦ by
      have := hx (e P)
      simp only [Equiv.symm_apply_apply] at this
      exact this
    obtain ⟨c, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x hall
    have hint : IsIntegral O (algebraMap C K c) := c.2
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (R := O) (K := L) hint, Polynomial.coeff_map]
    exact ((minpoly O (algebraMap C K c)).coeff i).2

end ValuationExtension
end GroupApproximation

#audit_axioms GroupApproximation.ValuationExtension.isPrincipalIdealRing_valuationSubring
#audit_axioms GroupApproximation.ValuationExtension.exists_places_over
