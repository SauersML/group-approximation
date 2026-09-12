import Mathlib.Tactic.LinearCombination
import GroupApproximation.GroupTheory.HigmanThompson.PLMoves
import GroupApproximation.Meta.AxiomGuard

/-!
# Residue congruences for orbits in `Γ₂`

Hyde–Lodha's residue invariant `θ_n` is recorded as `HigmanThompson.ResEq m x y`,
`x - y ∈ (n - 1) ℤ[1/n]` for `n = m + 2`; for `Γ₂` (`n = 6`, `m = 4`) this is congruence mod
`5 ℤ[1/6]`.

* `resEq_zero_of_resEq_two_mul_one_sub`: `z₁ ≡ 2 (1 - z₂)` and `z₂ ≡ 1 - z₁` give `z₁ ≡ 0`.  Indeed
  `z₁ = 2 (z₂ - (1 - z₁)) - (z₁ - 2 (1 - z₂))`, and `(n - 1) ℤ[1/n]` is closed under integer
  combinations.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- **`z₁ ≡ 2(1 - z₂)` and `z₂ ≡ 1 - z₁` force `z₁ ≡ 0`**, mod `(n - 1) ℤ[1/n]`, `n = m + 2`
(for `Γ₂`, mod `5 ℤ[1/6]`). -/
theorem resEq_zero_of_resEq_two_mul_one_sub {m : ℕ} {z₁ z₂ : ℚ}
    (h₁ : ResEq m z₁ (2 * (1 - z₂))) (h₂ : ResEq m z₂ (1 - z₁)) : ResEq m z₁ 0 := by
  obtain ⟨N₁, k₁, hk₁⟩ := h₁
  obtain ⟨N₂, k₂, hk₂⟩ := h₂
  refine ⟨N₁ + N₂, 2 * k₂ * ((m : ℤ) + 2) ^ N₁ - k₁ * ((m : ℤ) + 2) ^ N₂, ?_⟩
  push_cast
  rw [pow_add]
  linear_combination (-(((m : ℚ) + 2) ^ N₂)) * hk₁ + 2 * ((m : ℚ) + 2) ^ N₁ * hk₂

#audit_axioms GroupApproximation.HydeLodha.resEq_zero_of_resEq_two_mul_one_sub

end HydeLodha
end GroupApproximation
