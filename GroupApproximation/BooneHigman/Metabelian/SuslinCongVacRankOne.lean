import GroupApproximation.BooneHigman.Metabelian.SuslinCongLocGen
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2: trace-2 elements of `SL₂` over a GCD domain are rank-one unipotents

Lane `bh-met-92a`.

Over a GCD domain `S`, every `M ∈ M₂(S)` with `det M = 1` and `tr M = 2` has the form
`1 + x yᵀ` with `y ⬝ᵥ x = 0`.  Write `M - 1 = [[α, β], [γ, -α]]` (so `α² + βγ = 0`),
`g = gcd(α, β)`, `α = g a'`, `β = g b'` with `a', b'` relatively prime.  Cancelling `g` gives
`α a' + b' γ = 0`, so `a' ∣ b' γ`, hence `a' ∣ γ`, `γ = a' c`, and `-α = c b'`; so
`M - 1 = (g, c)ᵀ (a', b')`.

* `suslinCongVac_core`: the factorization `α = g r₀, β = g r₁, γ = h r₀, -α = h r₁`.
* `suslinCongVac_rankOne_of_trace`: `det M = 1`, `tr M = 2` ⟹ `M = 1 + x yᵀ`, `y ⬝ᵥ x = 0`.
* `suslinCongVac_mem_of_trace`: such `σ ∈ GL₂(S)` lie in `SuslinCongLocGen A S`.
* `suslinCongVac_elem_mem`: `E₂(S) ⊆ SuslinCongLocGen A S`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- **Factorization of a nilpotent `2 × 2` matrix over a GCD domain.** -/
theorem suslinCongVac_core {S : Type*} [CommRing S] [IsDomain S] [IsGCDMonoid S]
    (α β γ : S) (hsq : α * α + β * γ = 0) :
    ∃ g h r₀ r₁ : S, α = g * r₀ ∧ β = g * r₁ ∧ γ = h * r₀ ∧ -α = h * r₁ := by
  obtain ⟨_⟩ := ‹IsGCDMonoid S›
  obtain ⟨a', b', ha, hb, hu⟩ := extract_gcd α β
  by_cases hg : gcd α β = 0
  · have hα : α = 0 := by rw [ha, hg, zero_mul]
    have hβ : β = 0 := by rw [hb, hg, zero_mul]
    refine ⟨0, 1, γ, 0, ?_, ?_, ?_, ?_⟩
    · rw [hα, zero_mul]
    · rw [hβ, zero_mul]
    · rw [one_mul]
    · rw [hα, neg_zero, mul_zero]
  · have hrel : IsRelPrime a' b' := gcd_isUnit_iff_isRelPrime.mp hu
    have h1 : gcd α β * (α * a' + b' * γ) = 0 := by
      linear_combination hsq - α * ha - γ * hb
    have h2 : α * a' + b' * γ = 0 := (mul_eq_zero.mp h1).resolve_left hg
    by_cases ha0 : a' = 0
    · have hγ : b' * γ = 0 := by
        rw [ha0, mul_zero, zero_add] at h2
        exact h2
      have hb0 : b' ≠ 0 := by
        rintro rfl
        exact not_isUnit_zero (hrel (show (0 : S) ∣ a' by simp [ha0]) (dvd_refl 0))
      have hγ0 : γ = 0 := (mul_eq_zero.mp hγ).resolve_left hb0
      have hα0 : α = 0 := by rw [ha, ha0, mul_zero]
      refine ⟨gcd α β, 0, a', b', ha, hb, ?_, ?_⟩
      · rw [hγ0, zero_mul]
      · rw [hα0, neg_zero, zero_mul]
    · obtain ⟨c, hc⟩ := hrel.dvd_of_dvd_mul_left
        (show a' ∣ b' * γ from ⟨-α, by linear_combination h2⟩)
      have h5 : a' * (c * b' + α) = 0 := by linear_combination h2 - b' * hc
      have h6 : c * b' + α = 0 := (mul_eq_zero.mp h5).resolve_left ha0
      refine ⟨gcd α β, c, a', b', ha, hb, ?_, ?_⟩
      · rw [hc]
        ring
      · linear_combination -h6

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_core

/-- **Trace-2 elements of `SL₂` over a GCD domain are rank-one unipotents.** -/
theorem suslinCongVac_rankOne_of_trace {S : Type*} [CommRing S] [IsDomain S] [IsGCDMonoid S]
    (M : Matrix (Fin 2) (Fin 2) S) (hdet : M.det = 1) (htr : M 0 0 + M 1 1 = 2) :
    ∃ x y : Fin 2 → S, y ⬝ᵥ x = 0 ∧ M = 1 + Matrix.vecMulVec x y := by
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨g, h, r₀, r₁, hα, hβ, hγ, hδ⟩ := suslinCongVac_core (M 0 0 - 1) (M 0 1) (M 1 0)
    (by linear_combination -hdet + M 0 0 * htr)
  refine ⟨![g, h], ![r₀, r₁], ?_, ?_⟩
  · have hd : ![r₀, r₁] ⬝ᵥ ![g, h] = r₀ * g + r₁ * h := by simp
    rw [hd]
    linear_combination -hα - hδ
  · have e00 : M 0 0 = 1 + g * r₀ := by linear_combination hα
    have e11 : M 1 1 = 1 + h * r₁ := by linear_combination htr + hδ
    refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, e00, e11, hβ, hγ]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_rankOne_of_trace

/-- `E₂(S)` lies in `SuslinCongLocGen A S`. -/
theorem suslinCongVac_elem_mem {A S : Type*} [CommRing A] [CommRing S]
    {σ : (Matrix (Fin 2) (Fin 2) S)ˣ} (hσ : σ ∈ elementaryGroup (Fin 2) S) :
    σ ∈ SuslinCongLocGen A S := by
  rw [SuslinCongLocGen]
  exact Subgroup.subset_normalClosure (Set.mem_union_left _ (Set.mem_union_left _ hσ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_elem_mem

/-- **Every trace-2 element of `SL₂(S)`, `S` a GCD domain, lies in `SuslinCongLocGen A S`.** -/
theorem suslinCongVac_mem_of_trace {A S : Type*} [CommRing A] [CommRing S] [IsDomain S]
    [IsGCDMonoid S] (σ : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (hdet : Matrix.det (σ : Matrix (Fin 2) (Fin 2) S) = 1)
    (htr : (σ : Matrix (Fin 2) (Fin 2) S) 0 0 + (σ : Matrix (Fin 2) (Fin 2) S) 1 1 = 2) :
    σ ∈ SuslinCongLocGen A S := by
  obtain ⟨x, y, hyx, hσ⟩ := suslinCongVac_rankOne_of_trace _ hdet htr
  rw [SuslinCongLocGen]
  exact Subgroup.subset_normalClosure
    (Set.mem_union_left _ (Set.mem_union_right _ ⟨x, y, hyx, hσ⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongVac_mem_of_trace

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
