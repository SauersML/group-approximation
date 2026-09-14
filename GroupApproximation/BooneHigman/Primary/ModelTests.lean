import GroupApproximation.BooneHigman.Primary.Coprimary
import Mathlib.Data.ZMod.Basic

/-!
# Model tests for `IsCoprimaryWith`

* `int_isCoprimaryWith_bot`: `ℤ` is coprimary over itself with prime `⊥` and exponent `1`.
* `zmod_six_not_isCoprimaryWith`: `ℤ/6` is coprimary over `ℤ` for no ideal and no exponent, because
  `2` and `3` both kill a nonzero element and so would both lie in the prime.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Primary

/-- Positive model: `ℤ` is coprimary over itself with prime `⊥` and exponent `1`. -/
theorem int_isCoprimaryWith_bot : IsCoprimaryWith ℤ ℤ ⊥ 1 where
  nontrivial := inferInstance
  isPrime := Ideal.isPrime_bot
  smul_eq_zero_of_mem_pow r hr x := by
    rw [pow_one, Ideal.mem_bot] at hr
    simp [hr]
  smul_injective_of_notMem r hr x y hxy := by
    rw [Ideal.mem_bot] at hr
    simp only [smul_eq_mul] at hxy
    exact mul_left_cancel₀ hr hxy

/-- Negative model: `ℤ/6` is coprimary over `ℤ` for no ideal and no exponent. -/
theorem zmod_six_not_isCoprimaryWith (P : Ideal ℤ) (e : ℕ) :
    ¬ IsCoprimaryWith ℤ (ZMod 6) P e := by
  intro h
  have h2 : (2 : ℤ) ∈ P := by
    by_contra h2
    exact absurd (h.smul_injective_of_notMem 2 h2 (a₁ := 3) (a₂ := 0) (by decide))
      (by decide)
  have h3 : (3 : ℤ) ∈ P := by
    by_contra h3
    exact absurd (h.smul_injective_of_notMem 3 h3 (a₁ := 2) (a₂ := 0) (by decide))
      (by decide)
  exact h.isPrime.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using P.sub_mem h3 h2))

end Primary
end BooneHigman
end GroupApproximation
