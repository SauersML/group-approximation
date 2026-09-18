import Mathlib.Data.Nat.Find
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeSplit
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEStatement
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEBase
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEOne
import GroupApproximation.Meta.AxiomGuard

/-!
# `PureCharPrimeSplitStatement` from the exponent-`p` and high-exponent statements (bh-met-26)

Endpoint: `pureCharPrimeSplit_of_eOne_high`.

Route.  Given `H ≤ B ⋊[φ] Q` with `inr Q ≤ H`, pass to `eBase H ⋊[eBaseAut H hQ] Q ≅ H`
(`PureCharPrimeEBase`).  This group is f.g., and its base is abelian and killed by `p ^ e`.
Let `k` be the least exponent with `b ^ p ^ k = 1` on the base.

* `k ≤ 1`: the base has exponent `p`, and `exists_gl_of_exponent_prime` (from
  `PureCharPrimeEOneStatement`, proved in `PureCharPrimeEOne`) applies.
* `k ≥ 2`: minimality gives `b` with `b ^ p ^ (k - 1) ≠ 1`, and `PureCharPrimeEHighStatement`
  applies.

The two residual statements are justified (true, strictly smaller) in `PureCharPrimeEStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

theorem pureCharPrimeSplit_of_eOne_high (h1 : PureCharPrimeEOneStatement)
    (hh : PureCharPrimeEHighStatement) : PureCharPrimeSplitStatement := by
  intro B Q _ _ φ hB hQ p hp e hexp H hH hQle
  refine exists_gl_of_eBase H hQle ?_
  have hfg : Group.FG (eBase H ⋊[eBaseAut H hQle] Q) := eBase_fg H hQle hH
  have hB0 : ∀ a b : eBase H, a * b = b * a := eBase_comm H hB
  classical
  have hex : ∃ k : ℕ, ∀ b : eBase H, b ^ (p ^ k) = 1 := ⟨e, eBase_pow H (p ^ e) hexp⟩
  by_cases hk : Nat.find hex ≤ 1
  · have hexp1 : ∀ b : eBase H, b ^ p = 1 := by
      intro b
      rw [← pow_one p, ← pow_mul_pow_sub p hk, pow_mul, Nat.find_spec hex b, one_pow]
    exact exists_gl_of_exponent_prime h1 (eBaseAut H hQle) hB0 hQ hp hexp1 hfg
  · have hk2 : 2 ≤ Nat.find hex := by omega
    have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hmin : ∃ b : eBase H, b ^ (p ^ (Nat.find hex - 1)) ≠ 1 :=
      Classical.not_forall.mp (Nat.find_min hex hlt)
    exact hh (↥(eBase H)) Q (eBaseAut H hQle) hB0 hQ p hp (Nat.find hex) hk2
      (Nat.find_spec hex) hmin hfg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharPrimeSplit_of_eOne_high

end GroupApproximation.BooneHigman.Metabelian.Coprimary
