import GroupApproximation.AlgTop.ChernNewtonIdentity
import GroupApproximation.AlgTop.ChernParityAlgebra

/-!
# Discharging the Newton hypothesis of the parity chain

`GroupApproximation.ChernParityAlgebra.chern_eq_of_chernChar_sq_zero` proves the
manuscript's (2.7) — `c_q = (-1)^{q-1} (q-1)! ch_q` under a square-zero Chern
character — from a `NewtonIdentity` **hypothesis**.  This file supplies that
hypothesis as a theorem for every `GroupApproximation.AlgTop.TotalChern`, so the
statement below carries no algebraic assumption at all: only the square-zero
condition, which is the manuscript's `z² = 0`.

The proof of Newton's identity is in
`GroupApproximation.AlgTop.TotalChern.natCast_mul_chernClass`; it is the
coefficientwise form of the logarithmic-derivative identity `c · N(c) = X c'`,
and it needs neither Chern roots nor the splitting principle, so it applies to
the virtual class `δ = [W] - [p^*V]` exactly as it does to a bundle.

## Main declarations

* `TotalChern.newtonIdentity_chernChar` — the structure, built.
* `TotalChern.chernClass_eq_of_chernChar_sq_zero` — (2.7) with no Newton
  hypothesis.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open scoped Nat

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Every total Chern class over a `ℚ`-algebra satisfies Newton's identity,
paired with the Chern character `ch_q = p_q / q!`.  There is no splitting
hypothesis: virtual classes are covered. -/
theorem newtonIdentity_chernChar (c : TotalChern A) :
    ChernParityAlgebra.NewtonIdentity c.chernClass c.chernChar :=
  ⟨c.chernClass_zero, fun q hq => c.newton_identity_range q hq⟩

/-- **(2.7), unconditionally.**  If the positive-degree components of the Chern
character annihilate one another — which is what `z² = 0` gives for the virtual
class of the mapping torus — then `c_q = (-1)^{q-1} (q-1)! ch_q`. -/
theorem chernClass_eq_of_chernChar_sq_zero (c : TotalChern A)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j → c.chernChar i * c.chernChar j = 0) :
    ∀ q : ℕ, 0 < q →
      c.chernClass q = (-1 : A) ^ (q - 1) * (((q - 1)! : ℕ) : A) * c.chernChar q :=
  ChernParityAlgebra.chern_eq_of_chernChar_sq_zero (newtonIdentity_chernChar c) hsq

end

end TotalChern
end AlgTop
end GroupApproximation
