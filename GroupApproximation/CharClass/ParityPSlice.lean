import Mathlib.Algebra.Polynomial.Expand
import GroupApproximation.CharClass.ParityEvenSlice
import GroupApproximation.CharClass.ParityPData

/-!
# The slice class mod `p`: Frobenius support, and the top index

The bundle `W` restricts on the slice `{1} × S^{2n+1} × Y` to `V = 1^{n+1} ⊕ ⨁_j L_j^{⊕ d_j}`,
whose total mod-`p` Chern class is the slice class

```text
A = ∏_j (1 + h_j)^{d_j} ∈ H^*(Y; F_p),      Y = ∏_j CP^{d_j},  |h_j| = 2,
```

carried by `CharClass/ParityEvenSlice.lean`'s `sliceClass` as a polynomial whose `q`-th
coefficient is the degree-`2q` component.  This file supplies the two facts about `A` that
`CharClass/ParityPData.lean` consumes, at a general prime:

* **(A)**, the hypothesis `ParityPData.a_eq_zero`.  If `p ∣ d_j` for every `j` then
  `A = (∏_j (1 + h_j)^{d_j/p})^p` is a `p`-th power, so in characteristic `p` its
  coefficients are supported in indices divisible by `p`.  This is `sp-design` §3.3's L1
  and L3a; it is the exact analogue of `sliceClass_coeff_odd_eq_zero`, with the mod-2
  antidiagonal argument replaced by `Polynomial.map_frobenius_expand`.
* The vanishing above the top index, which `ParityEvenSlice.lean` already proves in a
  characteristic-free way (`sliceClass_coeff_eq_zero_of_lt`).

Together with `ParityPData.gamma_rank_eq_zero` these give the tower-facing endpoint
`ParityPData.gamma_top_eq_zero_of_slice`, the general-`p` replacement for
`ParityData.gamma_top_eq_zero_of_slice`.

For the tower `d_j = n · 2^j` a single hypothesis `p ∣ n` supplies everything: `p ∣ d_j`
for every `j` and every stage, and `p ∣ ∑_j d_j`.  Nothing below mentions the stage.

## Main results

* `GroupApproximation.CharClass.ParityP.coeff_pow_expChar_eq_zero` — Frobenius support of a
  `p`-th power.
* `ParityP.sliceClass_coeff_eq_zero_of_not_dvd` — hypothesis **(A)** for the slice class.
* `ParityPData.gamma_top_eq_zero_of_slice` — Step D mod `p` at the top index of a stage.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

section Frobenius

variable {R : Type*} [CommRing R]

/-- **Frobenius support.**  In characteristic `p` the coefficients of a `p`-th power live
in indices divisible by `p`: expanding, `f^p` is the image under the Frobenius of
`f(X^p)`, whose coefficients away from the multiples of `p` are zero. -/
theorem coeff_pow_expChar_eq_zero (p : ℕ) [ExpChar R p] (hp : 0 < p) (f : Polynomial R)
    {q : ℕ} (hq : ¬ p ∣ q) : (f ^ p).coeff q = 0 := by
  rw [← Polynomial.map_frobenius_expand p f, Polynomial.coeff_map,
    Polynomial.coeff_expand hp, if_neg hq]
  exact map_zero _

/-- Every exponent divisible by `p` makes the slice class a `p`-th power.  At `p = 2` this
is `sliceClass_eq_mul_self`. -/
theorem sliceClass_eq_pow (p : ℕ) {J : Type*} (u : Finset J) (h : J → R) (d : J → ℕ)
    (hd : ∀ j ∈ u, p ∣ d j) :
    sliceClass u h d
      = (∏ j ∈ u, (1 + Polynomial.C (h j) * Polynomial.X) ^ (d j / p)) ^ p := by
  rw [sliceClass_def, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [← pow_mul, Nat.div_mul_cancel (hd j hj)]

/-- **Hypothesis (A) of `ParityPData`.**  If every `d_j` is divisible by `p` then the
components of the slice class in indices not divisible by `p` vanish.  This is
`sp-design` §3.3's L1 + L3a, and the general-`p` form of
`sliceClass_coeff_odd_eq_zero`. -/
theorem sliceClass_coeff_eq_zero_of_not_dvd (p : ℕ) [ExpChar R p] (hp : 0 < p)
    {J : Type*} (u : Finset J) (h : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    {q : ℕ} (hq : ¬ p ∣ q) : (sliceClass u h d).coeff q = 0 := by
  rw [sliceClass_eq_pow p u h d hd]
  exact coeff_pow_expChar_eq_zero p hp _ hq

end Frobenius

end ParityP

/-! ## The tower-facing endpoint -/

namespace ParityPData

variable {p : ℕ} {R H : Type*} [CommRing R] [CommRing H]

/-- **Step D mod `p`, at the top index of a stage.**  The rank at a stage is
`r = n + 1 + m` with `m = ∑_j d_j`; `p ∣ n` and `p ∣ d_j` for every `j` give `r ≡ 1 mod p`,
and the slice class vanishes above `m`, so `γ_r(W) = 0`.

Nothing here depends on the stage: for the tower `d_j = n · 2^j` the hypothesis `p ∣ n`
gives `p ∣ d_j` at every `j` of every stage.  This is the general-`p` replacement for
`ParityData.gamma_top_eq_zero_of_slice`. -/
theorem gamma_top_eq_zero_of_slice (D : ParityPData p R H) {n : ℕ} (hn : p ∣ n)
    {J : Type*} (u : Finset J) (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) :
    D.γ (n + 1 + ∑ j ∈ u, d j) = 0 := by
  refine D.gamma_rank_eq_zero hn (Finset.dvd_sum hd) ?_
  rw [hslice]
  exact sliceClass_coeff_eq_zero_of_lt u gen d (by omega)

end ParityPData

end GroupApproximation.CharClass
