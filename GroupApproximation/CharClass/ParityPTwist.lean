import Mathlib.Data.Nat.Choose.Sum
import GroupApproximation.CharClass.ParityPNewtonValue

/-!
# L4a, step four: the twist `y ↦ y + κ·y^p` on power sums

`sp-design`'s L4a proof runs the substitution `φ_κ : y ↦ y + κ·y^p` through the
indecomposables.  Two facts about `φ_κ` are needed and this file proves the first, which is
the elementary one: its effect on a power sum is the binomial theorem and nothing else.

```text
  φ_κ(p_b)  =  ∑_{j ≤ b}  κ^{b-j} · C(b,j) · p_{j + p(b-j)} .
```

There is no symmetric-function theory in it: `p_b = ∑_k y_k^b`, and each summand expands by
`add_pow`.  The reindexing is `(b − j) + p(b − j)`-free: with `add_pow`'s own indexing the
surviving exponent is `j + p(b − j)`, which at `b = i+1` hits the weight `ip+1` exactly once,
at `j = 1`, with coefficient `C(i+1,1)·κ^i = (i+1)·κ^i`.  That single surviving term is what
the division by `i+1` in `ℤ[κ]` will later cancel.

The second fact about `φ_κ`, that it descends to the indecomposables because it is a ring
homomorphism, is free: `twist` is an `AlgHom` by construction.

## Main results

* `GroupApproximation.CharClass.ParityP.twist` — the substitution, as an `AlgHom`.
* `ParityP.twist_psum` — the binomial expansion on a power sum.
* `ParityP.twist_psum_weight` — the exponent bookkeeping: at `b = i+1` the weight `ip+1`
  occurs exactly at `j = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section Twist

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The substitution `y ↦ y + κ·y^p`, as an algebra endomorphism.  It is a ring
homomorphism by construction, which is the only structural fact `sp-design`'s proof uses
about it. -/
noncomputable def twist (R : Type*) [CommRing R] (n p : ℕ) (κ : R) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (fun k => X k + C κ * X k ^ p)

theorem twist_X (p : ℕ) (κ : R) (k : Fin n) :
    twist R n p κ (X k) = X k + C κ * X k ^ p := aeval_X _ _

/-- **The twist on a power sum.**  One application of the binomial theorem to each
summand of `p_b = ∑_k y_k^b`, then a swap of the two sums. -/
theorem twist_psum (p : ℕ) (κ : R) (b : ℕ) :
    twist R n p κ (psum (Fin n) R b)
      = ∑ j ∈ Finset.range (b + 1),
          C (κ ^ (b - j)) * (b.choose j : MvPolynomial (Fin n) R)
            * psum (Fin n) R (j + p * (b - j)) := by
  have hterm : ∀ k : Fin n,
      twist R n p κ (X k ^ b)
        = ∑ j ∈ Finset.range (b + 1),
            C (κ ^ (b - j)) * (b.choose j : MvPolynomial (Fin n) R)
              * X k ^ (j + p * (b - j)) := by
    intro k
    rw [map_pow, twist_X, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← pow_mul, ← C_pow, pow_add]
    ring
  rw [psum, map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [psum, Finset.mul_sum]

/-- **The exponent bookkeeping.**  For `p ≥ 2` and `b = i + 1`, the weight `i·p + 1` is
reached by exactly one term of `twist_psum`, the one at `j = 1`, whose coefficient is
`C(i+1,1)·κ^i = (i+1)·κ^i`.  Writing `p = q + 1` turns the statement into the linear
identity `q·m = q·i` in the two atoms `q·m` and `q·i`, and `q ≥ 1` cancels it. -/
theorem twist_psum_weight {p : ℕ} (hp : 2 ≤ p) (i j : ℕ) (hjb : j ≤ i + 1) :
    j + p * (i + 1 - j) = i * p + 1 ↔ j = 1 := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, i + 1 - j = m := ⟨i + 1 - j, rfl⟩
  have hjm : j + m = i + 1 := by omega
  have hcomm : q * i = i * q := Nat.mul_comm q i
  have e1 : (q + 1) * m = q * m + m := by ring
  have e2 : i * (q + 1) = i * q + i := by ring
  rw [hm, hq, e1, e2]
  constructor
  · intro h
    have hqm : q * m = q * i := by omega
    have hmi : m = i := Nat.eq_of_mul_eq_mul_left (by omega) hqm
    omega
  · intro h
    have hmi : m = i := by omega
    rw [hmi] at *
    omega

end Twist

end ParityP

end GroupApproximation.CharClass
