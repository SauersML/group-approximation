---
rg: 2
id: thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof
kind: route
title: Weighted coset test at t = -1/lambda, Guba's shift to K[M_1], and a dimension count in a letter window
target: thompson-f-twisted-x0-binomial-is-ore-with-every-element
requires: []
---

Notation as in the target.
- `M` is the positive monoid `<x_0, x_1, ... | x_j x_i = x_i x_(j+1), i < j>`. Its elements
  have unique normal forms `x_(i_1) ... x_(i_s)` with `i_1 <= ... <= i_s`, and `M` embeds
  in `F` (Cannon--Floyd--Parry §1; survey arXiv:2305.07113 §1.5).
- `M_1` is the submonoid on letters `>= 1`, and `phi(x_i) = x_(i+1)`.
- `R` is a domain because `F` is left-orderable.
- Put `mu = -1/lambda`. Then `1 + lambda x_0 = lambda (x_0 - mu)`, so the ideal is
  `J = (x_0 - mu) R`.

**Step 1. Weighted coset test.** `y` lies in `J` iff, for every right coset `C = <x_0> g`,
`sum_n y(x_0^n g) mu^n = 0`.
- Identify `C` with `Z` and write `Y(t) = sum_n y(x_0^n g) t^n`, similarly `U(t)`.
- The coefficient of `(x_0 - mu) u` at `x_0^n g` is `u(x_0^(n-1) g) - mu u(x_0^n g)`, so on
  `C` the ideal is `(t - mu) K[t, t^-1]`.
- A Laurent polynomial is divisible by `t - mu` iff it vanishes at `mu`, and `mu ≠ 0`.

*Consequence.* `x_0^k y - mu^k y` lies in `J` for all `y` and all `k`, because
`t^k - mu^k` is divisible by `t - mu`.

**Step 2. Normalization (Guba's reduction).**
- By the survey's Lemma 3.8, `b R = b g R` for some `g` with `supp(b g) ⊆ M`, so assume
  `supp b ⊆ M`.
- Write each monomial as `x_0^(a_t) m'_t` with `m'_t` in `M_1`, and set
  `b' = sum_t b_t mu^(a_t) m'_t`. By Step 1, `b v - b' v` lies in `J` for every `v`.
- If `b' = 0`, then `b` itself lies in `J ∩ b R` and is nonzero.
- Otherwise it suffices to find `v ≠ 0` with `b' v` in `J`.

**Step 3. Shift.** For `j >= 1`, `x_0^-1 x_j x_0 = x_(j+1)`, so `b' x_0^k = x_0^k phi^k(b')`.

**Step 4. Dependence gives a solution.** Suppose `r_0, ..., r_N` in `K[M_1]` are not all
zero and `sum_k phi^k(b') r_k = 0`. Put `v = sum_k mu^-k x_0^k r_k`.
- `b' v = sum_k mu^-k x_0^k phi^k(b') r_k`.
- By Step 1 this is congruent to `sum_k phi^k(b') r_k = 0` modulo `J`.
- `v ≠ 0`, because the normal forms `x_0^k m` with `m` in `M_1` are distinct for distinct
  `(k, m)`.

**Step 5. Dimension count.** Let the monomials of `b'` have letters `<= I` and degrees in
`{0, ..., D}`. Choose `L`, and let `c = floor(L/2)` and `N = L - I - c - D`. Let `A` be
the set of normal forms of degree `c` with letters in `[1, L]`.
- *Where the products land.* Inserting a letter `x_j` into a word of length `l` gives a
  normal form whose new letter is at most `j + l`, and the existing letters are unchanged.
  So for `k <= N`, `a` in `A`, and a monomial `t` of `phi^k(b')` of degree `d`, the product
  `t a` is a normal form of degree `c + d` with letters in `[1, I + N + c + D] = [1, L]`.
- *Sizes.* The unknowns `(r_k)` with `r_k` in `K[A]` span a space of dimension
  `(N + 1) binom(L + c - 1, c)`. The target has dimension at most
  `sum_(d=0)^D binom(L + c + d - 1, c + d)`.
- *Ratio.* `binom(L+c+d-1, c+d) / binom(L+c-1, c) = prod_(j=1)^d (L+c-1+j)/(c+j)`. Each
  factor is at most `(3L + 2D)/(L + 1) <= 4` once `L + 1 >= 2D`.
- *Conclusion.* The target has dimension at most `(4^(D+1)/3) |A|`, while
  `N + 1 >= L/2 - I - D`. For `L` large the linear map has a nonzero kernel, and Step 4
  applies.

**Credit and trust surfaces.**
- Steps 2–4 are Guba's proof of Theorem 2 in arXiv:2201.02308 §3, with the `mu`-weights
  added.
- Quoted: the normal form of `M`, the embedding `M ⊆ F`, the survey's Lemma 3.8, and
  left-orderability of `F`.
- Everything else is proved above.
