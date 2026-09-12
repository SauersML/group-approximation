import GroupApproximation.CharClass.OddPTotalProducer
import GroupApproximation.CharClass.OddPCartanVanish

/-!
# The input `BadTwoOddP`: V in degree two

In degree two the class `[D_j h]` vanishes at every even index `j ∉ {0, 2(p − 1)}`.

`OddPCartanVanish.oddDClass_eq_zero_of_not_dvd` (V, lane `lx-cartanvanish`) kills `[D_j x]` for x of
even degree whenever `p − 1 ∤ (j + 1)/2`.  At an even index `j ≤ 2p`, `(j + 1)/2 = j/2 ∈ [0, p]`.  Its
multiples of `p − 1` in that range are `0` and `p − 1` alone, because `2(p − 1) > p` when `p ≥ 3`, and
these are the indices `0` and `2(p − 1)`.  Above `2p` the family `oddDAdd` is zero by definition.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

theorem not_dvd_half_of_bad {p j : ℕ} (hp3 : 3 ≤ p) (hjev : j % 2 = 0) (hjle : j ≤ p * 2)
    (hj0 : j ≠ 0) (hj1 : j ≠ 2 * (p - 1)) : ¬ (p - 1) ∣ (j + 1) / 2 := by
  have hhalf : (j + 1) / 2 = j / 2 := by omega
  rw [hhalf]
  rintro ⟨m, hm⟩
  rcases m with _ | _ | m
  · omega
  · omega
  · have h2 : (p - 1) * 2 ≤ j / 2 := by
      rw [hm]
      exact Nat.mul_le_mul_left (p - 1) (by omega)
    omega

/-- **`BadTwoOddP` at every odd prime**, from V. -/
theorem badTwoOddP (p : ℕ) [Fact p.Prime] (hp : Odd p) : BadTwoOddP p hp := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    have ho := Nat.odd_iff.mp hp
    omega
  intro X h j hjev hj0 hj1
  by_cases hjle : j ≤ p * 2
  · rw [oddDAdd_apply p hp X 2 j hjle]
    exact OddPCartanVanish.oddDClass_eq_zero_of_not_dvd p hp 2 j even_two hjle
      (not_dvd_half_of_bad hp3 hjev hjle hj0 hj1) h
  · exact oddDAdd_of_lt p hp X 2 j (by omega) h

end

end OddPTotal

#audit_axioms OddPTotal.not_dvd_half_of_bad
#audit_axioms OddPTotal.badTwoOddP

end CharClass
end GroupApproximation
