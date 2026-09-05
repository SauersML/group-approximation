import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Ring.Parity

import Mathlib.Tactic.Ring
/-!
# The parity of the mapping-torus Chern coefficient

Lemma 3 of the STW Problem LIX manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`)
turns on a single arithmetic fact.  For a virtual class `δ` over `S¹ × S⁵ × Y`
whose Chern character is `z · ch(β)` with `z² = 0`, the Chern classes are
`c_q(δ) = (-1)^{q-1} (q-1)! ch_q(δ)`, and for `β = ∏_j L_j^{a_j}` the coefficient
of `z ∏_j h_j^{b_j}` with `|b| = q - 3` is the manuscript's (2.8):

```text
(-1)^{q-1} · (|b| + 2)! / ∏_j b_j ! · ∏_j a_j^{b_j}.
```

The manuscript asserts "It is an even integer."  This file proves exactly that,
and it proves it in the sharp form the manuscript uses, namely by factoring the
coefficient as

```text
(|b| + 2)! / ∏_j b_j !  =  (|b| + 2)(|b| + 1) · multinomial(|b|; b),
```

so the parity comes from the product of the two *consecutive* integers
`|b| + 1` and `|b| + 2` and not from any property of the multi-index.

Everything here is pure arithmetic: there is no topology, no cohomology and no
`Chern` anything, so it is unconditional and independent of the rest of the
foundation.

## Main declarations

* `prod_factorial_mul_coeff` — the exact factorization, cleared of division.
* `factorial_add_two_div_prod_factorial` — the displayed identity above.
* `even_factorial_add_two_div_prod_factorial` — (2.8) is even.
* `two_dvd_chernCoefficient` — the signed coefficient with its monomial
  `∏_j a_j^{b_j}` attached, as an even integer.
-/

namespace GroupApproximation
namespace AlgTop

open Finset
open scoped Nat

variable {ι : Type*} (s : Finset ι) (b : ι → ℕ)

/-- The coefficient `(|b| + 2)! / ∏_j b_j !` of the manuscript's (2.8), with the
division cleared: `∏_j b_j !` times `(|b|+2)(|b|+1) multinomial(|b|; b)` is
`(|b|+2)!`. -/
theorem prod_factorial_mul_coeff :
    (∏ j ∈ s, (b j)!) *
        (((∑ j ∈ s, b j) + 2) * ((∑ j ∈ s, b j) + 1) * Nat.multinomial s b)
      = ((∑ j ∈ s, b j) + 2)! := by
  have hspec : (∏ j ∈ s, (b j)!) * Nat.multinomial s b = (∑ j ∈ s, b j)! :=
    Nat.multinomial_spec s b
  calc
    (∏ j ∈ s, (b j)!) *
          (((∑ j ∈ s, b j) + 2) * ((∑ j ∈ s, b j) + 1) * Nat.multinomial s b)
        = ((∑ j ∈ s, b j) + 2) * (((∑ j ∈ s, b j) + 1) *
            ((∏ j ∈ s, (b j)!) * Nat.multinomial s b)) := by ring
    _ = ((∑ j ∈ s, b j) + 2) * (((∑ j ∈ s, b j) + 1) * (∑ j ∈ s, b j)!) := by
          rw [hspec]
    _ = ((∑ j ∈ s, b j) + 2)! := by
          rw [← Nat.factorial_succ, ← Nat.factorial_succ]

/-- The manuscript's coefficient, written out:
`(|b| + 2)! / ∏_j b_j ! = (|b| + 2)(|b| + 1) · multinomial(|b|; b)`. -/
theorem factorial_add_two_div_prod_factorial :
    ((∑ j ∈ s, b j) + 2)! / (∏ j ∈ s, (b j)!)
      = ((∑ j ∈ s, b j) + 2) * ((∑ j ∈ s, b j) + 1) * Nat.multinomial s b := by
  rw [← prod_factorial_mul_coeff s b,
    Nat.mul_div_cancel_left _ (Nat.prod_factorial_pos s b)]

/-- **The manuscript's (2.8) is even.**  The two consecutive factors `|b| + 1`
and `|b| + 2` supply the factor of two; the multi-index plays no role. -/
theorem even_factorial_add_two_div_prod_factorial :
    Even (((∑ j ∈ s, b j) + 2)! / ∏ j ∈ s, (b j)!) := by
  rw [factorial_add_two_div_prod_factorial]
  refine Even.mul_right ?_ _
  have h : Even (((∑ j ∈ s, b j) + 1) * (((∑ j ∈ s, b j) + 1) + 1)) :=
    Nat.even_mul_succ_self _
  rwa [mul_comm] at h

/-- The signed coefficient of (2.8), monomial attached, as an even integer:
`(-1)^{q-1} · (|b|+2)!/∏ b_j ! · ∏_j a_j^{b_j}` is divisible by two.

This is the exact statement the mapping-torus parity lemma consumes: every
positive Chern class of the virtual class `δ` is an integral combination of
these coefficients, so every one of them is even. -/
theorem two_dvd_chernCoefficient (a : ι → ℤ) (q : ℕ) :
    (2 : ℤ) ∣ (-1) ^ q * (((∑ j ∈ s, b j) + 2)! / ∏ j ∈ s, (b j)! : ℕ) *
      ∏ j ∈ s, a j ^ b j := by
  obtain ⟨k, hk⟩ := even_factorial_add_two_div_prod_factorial s b
  refine ⟨(-1) ^ q * (k : ℤ) * ∏ j ∈ s, a j ^ b j, ?_⟩
  rw [hk]
  push_cast
  ring

end AlgTop
end GroupApproximation
