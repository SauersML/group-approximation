---
rg: 2
id: thompson-f-one-minus-x0-is-ore-with-every-element-proof
kind: route
title: Shift the coefficients past x_0 and count positive normal forms in a growing index window
target: thompson-f-one-minus-x0-is-ore-with-every-element
requires: []
---

Notation as in the target. `M` is the positive monoid `<x_0, x_1, ... | x_j x_i = x_i x_(j+1), i < j>`.
Every element of `M` has a unique normal form `x_(i_1) ... x_(i_s)` with
`i_1 <= ... <= i_s`, and `M` embeds in `F` (Cannon--Floyd--Parry §1). `M_1` is the
submonoid on letters `>= 1`. `R` is a domain because `F` is left-orderable.

**Step 1. Orbit test.** `y` lies in `(1 - x_0) R` iff, for every right coset
`C = <x_0> g`, the coefficient sum of `y` over `C` vanishes.
- *Only if.* Left multiplication by `x_0` permutes `C`, so `u - x_0 u` has sum 0 on `C`.
- *If.* Identify `C` with `Z` via `x_0^n g -> n`. A finitely supported zero-sum sequence
  is `u - x_0 u` for the finitely supported partial sums `u(x_0^n g) = sum_(m <= n) y(x_0^m g)`.

**Step 2. Normalizing `b`.** For `v` in `R`, whether `b v` lies in `(1 - x_0) R` depends
only on the image of `b` in `K[<x_0> \ F]`, by Step 1.
- *Right translation.* `b R = b g R` for `g` in `F`. Every finite subset of `F` has a
  right translate inside `M` (survey arXiv:2305.07113, Lemma 3.8, or directly from
  `F = M M^-1`), so assume `supp b ⊆ M`.
- *Removing leading `x_0`s.* A normal form is `x_0^a m'` with `m'` in `M_1`, and
  replacing each monomial by its `m'` does not change the image in `K[<x_0> \ F]`.
  Call the result `b'`, so `supp b' ⊆ M_1`.
- *The case `b' = 0`.* Then `b` itself lies in `(1 - x_0) R`, and `b` is a nonzero
  element of the intersection.
- Otherwise it suffices to find `v ≠ 0` with `b' v` in `(1 - x_0) R`, because then `b v`
  is in `(1 - x_0) R` and is nonzero.

**Step 3. Shift.** Let `phi(x_i) = x_(i+1)`. The relations give `x_0^-1 x_j x_0 = x_(j+1)`
for `j >= 1`. So `b' x_0^k = x_0^k phi^k(b')` for all `k >= 0`.

**Step 4. Dependence gives a solution.** Suppose `r_0, ..., r_N` in `K[M_1]` are not all
zero and `sum_k phi^k(b') r_k = 0`. Put `v = sum_k x_0^k r_k`.
- `b' v = sum_k x_0^k phi^k(b') r_k`.
- By Step 1, `x_0^k y ≡ y` modulo `(1 - x_0) R`, so `b' v ≡ sum_k phi^k(b') r_k = 0`.
- `v ≠ 0`: the words `x_0^k m` with `m` in `M_1` are normal forms, distinct for distinct
  `(k, m)`, so no cancellation occurs among the `x_0^k r_k`.

**Step 5. Counting.** Let `supp b'` have maximal letter `I` and degrees in `{0, ..., D}`.
Fix integers `L`, `c`, `N` with `L >= I + N + c + D`, and let `A` be the set of
normal forms of degree `c` with letters in `[1, L]`, so `|A| = binom(L + c - 1, c)`.
- *Where the products land.* Inserting one letter `x_j` into a word of length `l` gives a
  normal form whose new letter is at most `j + l`, and the old letters are unchanged.
  So for a monomial `t` of degree `d` in `supp phi^k(b')` (letters `<= I + k`) and `a` in
  `A`, the product `t a` is a normal form of degree `c + d` with letters in
  `[1, I + k + c + D] ⊆ [1, L]`.
- *The linear map.* `(r_k)_k -> sum_k phi^k(b') r_k` with `r_k` in `K[A]` goes from a space
  of dimension `(N + 1) |A|` into the span of normal forms of degrees `c..c+D` with letters
  in `[1, L]`. That span has dimension at most `sum_(d=0)^D binom(L + c + d - 1, c + d)`.
- *Ratio.* `binom(L+c+d-1, c+d) / binom(L+c-1, c) = prod_(j=1)^d (L+c-1+j)/(c+j)`.
- *Choice of constants.* Take `c = floor(L/2)` and `N = L - I - c - D`. Each factor is at
  most `(L + c + d)/(c + 1) <= 4` once `L >= 2D + 2`, so the target has dimension at most
  `(4^(D+1)/3) |A|`, while `N + 1 >= L/2 - I - D`.
- For `L` large, `(N + 1)|A|` exceeds the target dimension, the map has a nonzero kernel,
  and Step 4 applies.

**Remark (right half of the interval).** The same five steps prove
`(1 - x_1) R ∩ b R ≠ 0` whenever `supp b` lies in one right coset `F_[1/2,1] g`. Here
`F_[1/2,1] = <x_1, x_2, ...>` is the subgroup of elements supported in `[1/2, 1]`. Replace
`x_0` by `x_1`, `M_1` by `M_2`, and letters `[1, L]` by `[2, L]`; the relation
`x_1^-1 x_j x_1 = x_(j+1)` holds for `j >= 2`. This is recorded under the open claim
`thompson-f-one-minus-x1-is-ore-with-every-element`.

**Trust surfaces.**
- The normal form of `M` and the embedding `M ⊆ F` (Cannon--Floyd--Parry; survey
  arXiv:2305.07113 §1.5 and Lemma 3.8) are quoted.
- Left-orderability of `F` is quoted.
- Everything else is proved above.
