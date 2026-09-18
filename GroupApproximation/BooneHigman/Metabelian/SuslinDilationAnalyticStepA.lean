import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticConj
import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticPoly
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin dilation, analytic half, part 3: the dilation estimate on `E_N(S[Y])`

Lane `bh-met-76`.  Fix `φ : B → S` and `s ∈ B` such that every `c ∈ S` has `c φ(s)^t ∈ φ(B)`.
Levels `G_K` are taken for `φ : B[Y] → S[Y]` and `s` (`suslinDilAnLevel`).  For
`α ∈ E_N(S[Y])`, write `α_k = α(φ(s)^k Y)` and `α(0)` for the constant term.

**Estimate** (`suslinDilAn_estimate_of_mem`, `N ≥ 3`): for every `K'`, all large `k` give
`α_k α(0)⁻¹ ∈ G_{K'}`.  On `e_{ij}(f)` with `f - f(0) = Y g` and `g φ(s)^t = φ(h)`,
`f(φ(s)^k Y) - f(0) = φ(s^{K'} · s^r Y h(s^k Y))` for `k = K' + t + r`.  Products use
`x y (a b)⁻¹ = (x a⁻¹) · a (y b⁻¹) a⁻¹` and the commutator estimate for `a = α₁(0) ∈ E_N`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Estimate

variable {B S : Type*} [CommRing B] [CommRing S] (φ : B →+* S) (s : B) {N : ℕ}

/-- The estimate on one polynomial entry. -/
theorem suslinDilAn_gen_estimate (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    (f : Polynomial S) (K' : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ b : Polynomial B,
      suslinDilAnDilate (φ s ^ k) f - Polynomial.C (f.coeff 0) =
        Polynomial.mapRingHom φ (Polynomial.C s ^ K' * b) := by
  obtain ⟨g, hg⟩ : Polynomial.X ∣ f - Polynomial.C (f.coeff 0) := Polynomial.X_dvd_iff.2 (by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero, sub_self])
  obtain ⟨t, h, hh⟩ := suslinDilAn_surj_poly φ s hsurj g
  refine ⟨K' + t, fun k hk ↦ ?_⟩
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨Polynomial.C s ^ r * Polynomial.X * suslinDilAnDilate (s ^ (K' + t + r)) h, ?_⟩
  have e₁ : Polynomial.mapRingHom φ (Polynomial.C s) = Polynomial.C (φ s) := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
  have e₂ : Polynomial.mapRingHom φ Polynomial.X = Polynomial.X := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_X]
  have hD := RingHom.congr_fun (suslinDilAnDilate_comp_mapRingHom φ (s ^ (K' + t + r))) h
  rw [RingHom.comp_apply, RingHom.comp_apply, map_pow] at hD
  have hh' := congrArg (suslinDilAnDilate (φ s ^ (K' + t + r))) hh
  rw [map_mul, map_pow, e₁, suslinDilAnDilate_C, hD] at hh'
  have hf := congrArg (suslinDilAnDilate (φ s ^ (K' + t + r))) hg
  rw [map_sub, suslinDilAnDilate_C, map_mul, suslinDilAnDilate_X] at hf
  rw [hf]
  simp only [map_mul, map_pow, e₁, e₂]
  linear_combination (Polynomial.C (φ s) ^ (K' + r) * Polynomial.X) * hh'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_gen_estimate

/-- The dilation estimate for `α ∈ GL_N(S[Y])`: for each level `K'`, all large `k` give
`α(φ(s)^k Y) α(0)⁻¹ ∈ G_{K'}` (levels for `φ : B[Y] → S[Y]` and `s`). -/
def SuslinDilationAnalyticEstimate (φ : B →+* S) (s : B) (N : ℕ)
    (α : (Matrix (Fin N) (Fin N) (Polynomial S))ˣ) : Prop :=
  ∀ K' : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (φ s ^ k)) α *
        (elementaryMatrixUnitMap (ι := Fin N)
          ((Polynomial.C : S →+* Polynomial S).comp (Polynomial.constantCoeff (R := S))) α)⁻¹ ∈
      suslinDilAnLevel (Polynomial.mapRingHom φ) (Polynomial.C s) N K'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinDilationAnalyticEstimate

theorem suslinDilAn_estimate_unit (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    (i j : Fin N) (hij : i ≠ j) (f : Polynomial S) :
    SuslinDilationAnalyticEstimate φ s N (elementaryUnit i j hij f) := by
  intro K'
  obtain ⟨k₀, hk₀⟩ := suslinDilAn_gen_estimate φ s hsurj f K'
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨b, hb⟩ := hk₀ k hk
  rw [elementaryMatrixUnitMap_elementaryUnit, elementaryMatrixUnitMap_elementaryUnit,
    suslinDilAn_elementaryUnit_inv, elementaryUnit_mul]
  refine suslinDilAnLevel_unit (Polynomial.mapRingHom φ) (Polynomial.C s) i j hij b ?_
  rw [← hb, RingHom.comp_apply, Polynomial.constantCoeff_apply, sub_eq_add_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_estimate_unit

theorem suslinDilAn_estimate_one : SuslinDilationAnalyticEstimate φ s N 1 := fun _ ↦
  ⟨0, fun _ _ ↦ by
    simp only [map_one, inv_one, mul_one]
    exact one_mem _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_estimate_one

theorem suslinDilAn_estimate_mul (hN : 2 < N)
    (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    {α₁ α₂ : (Matrix (Fin N) (Fin N) (Polynomial S))ˣ}
    (hα₁ : α₁ ∈ elementaryGroup (Fin N) (Polynomial S))
    (h₁ : SuslinDilationAnalyticEstimate φ s N α₁)
    (h₂ : SuslinDilationAnalyticEstimate φ s N α₂) :
    SuslinDilationAnalyticEstimate φ s N (α₁ * α₂) := by
  intro K'
  have hκ : elementaryMatrixUnitMap (ι := Fin N)
      ((Polynomial.C : S →+* Polynomial S).comp (Polynomial.constantCoeff (R := S))) α₁ ∈
        elementaryGroup (Fin N) (Polynomial S) :=
    elementaryGroup_map_le (ι := Fin N)
      ((Polynomial.C : S →+* Polynomial S).comp (Polynomial.constantCoeff (R := S)))
      (Subgroup.mem_map_of_mem _ hα₁)
  obtain ⟨K, hK⟩ := suslinDilAn_conjBound_of_mem (Polynomial.mapRingHom φ) (Polynomial.C s) hN
    (suslinDilAn_surj_poly φ s hsurj) hκ K'
  obtain ⟨k₁, hk₁⟩ := h₁ K'
  obtain ⟨k₂, hk₂⟩ := h₂ K
  refine ⟨max k₁ k₂, fun k hk ↦ ?_⟩
  have hc := hK _ (hk₂ k (max_le_iff.1 hk).2)
  have h := mul_mem (hk₁ k (max_le_iff.1 hk).1) hc
  rw [map_mul, map_mul]
  convert h using 1
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_estimate_mul

/-- **The dilation estimate** (`N ≥ 3`) holds on all of `E_N(S[Y])`. -/
theorem suslinDilAn_estimate_of_mem (hN : 2 < N)
    (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    {α : (Matrix (Fin N) (Fin N) (Polynomial S))ˣ}
    (hα : α ∈ elementaryGroup (Fin N) (Polynomial S)) :
    SuslinDilationAnalyticEstimate φ s N α := by
  have hα' : α ∈ Subgroup.closure {z : (Matrix (Fin N) (Fin N) (Polynomial S))ˣ |
      ∃ (i j : Fin N) (h : i ≠ j) (a : Polynomial S), elementaryUnit i j h a = z} := hα
  refine Subgroup.closure_induction''
    (p := fun α _ ↦ SuslinDilationAnalyticEstimate φ s N α) ?_ ?_ ?_ ?_ hα'
  · rintro _ ⟨i, j, hij, c, rfl⟩
    exact suslinDilAn_estimate_unit φ s hsurj i j hij c
  · rintro _ ⟨i, j, hij, c, rfl⟩
    rw [suslinDilAn_elementaryUnit_inv]
    exact suslinDilAn_estimate_unit φ s hsurj i j hij (-c)
  · exact suslinDilAn_estimate_one φ s
  · intro x y hx _ hx' hy'
    exact suslinDilAn_estimate_mul φ s hN hsurj hx hx' hy'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_estimate_of_mem

end Estimate

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
