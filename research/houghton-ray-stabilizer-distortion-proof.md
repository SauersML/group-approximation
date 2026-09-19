---
rg: 2
id: houghton-ray-stabilizer-distortion-proof
kind: route
title: Bounded displacement plus bubble sort bounds the distortion of H_2 in H_3; BCMR's complexity estimate bounds H_k in H_n for k >= 3
target: houghton-ray-stabilizer-distortion-quadratic-then-log
requires:
  - houghton-word-length-is-complexity-up-to-log
artifacts:
  - experiments/houghton-corridor-cap-2026-09-17/referee_and_cap.py
  - experiments/houghton-corridor-cap-2026-09-17/referee_and_cap.out
---

Conventions as in the target: right actions, `λ_(a,b)` maps
`(a,p) ↦ (a,p-1)` for `p >= 2`, `(a,1) ↦ (b,1)`, `(b,p) ↦ (b,p+1)`.
Changing finite generating sets changes `Dist` only up to `≃`, so we may fix
generating sets.

## Part (b)

Let `3 <= k < n`, `b ∈ B_k`, `ℓ = |b|_S`. The complexity `P(b)` is the same
whether `b` is read in `H_n` or in `B_k ≅ H_k`, because the rays
`k+1, ..., n` contribute `p_i = 0` (`houghton-word-length-is-complexity-up-to-log`).
By the lower bound of Theorem 4.1 in `H_n` (`n >= 3`), `P(b) <= C ℓ`. If
`P(b) <= 1`, then `b` is trivial or a single `λ_(i,j)` with `i, j <= k`, so
`|b|_(S_k)` is bounded. Otherwise, by the upper bound of Theorem 4.1 in
`H_k` (`k >= 3`),

`|b|_(S_k) <= K P(b) log P(b) <= K C ℓ log(C ℓ)`.

So `Dist_(k,n)(ℓ) ≼ ℓ log ℓ`. ∎

The hypothesis `k >= 3` is used exactly once, in the upper bound in `H_k`.
For `k = 2` that bound is false (part (a)).

## Part (a), upper bound

**Metric.** On `Y_3` put `d((r,p),(r,q)) = |p-q|` and
`d((r,p),(s,q)) = p+q-1` for `r ≠ s`. This is the path metric of the graph
whose edges join consecutive points of a ray and join the three points
`(1,1), (2,1), (3,1)` pairwise. Each of `X^(±1)`, `Y^(±1)`, `α` moves every
point along at most one edge. So if `|b|_S = ℓ`, then `d(z, zb) <= ℓ` for all
`z`.

**Uniform depth.** A letter acts on `(r,q)` with `q >= 3` as the translation
`q ↦ q + t_r(letter)`: `λ_(a,b)` is non-uniform only at `(a,1)`, and `α` only
at depth `<= 2`. Along a word of length `ℓ`, depth changes by at most one per
letter. So for `p >= ℓ + 3` the trajectory of `(r,p)` stays on ray `r` at
depth `>= 3`, and `(r,p) b = (r, p + t_r(b))`.

**Straightening.** Let `b ∈ B_2`, so `b` fixes ray 3 pointwise, and put
`t = t_1(b) = -t_2(b)`. Identify `L = ray 2 ∪ ray 1` with `Z` by
`c(1,p) = p` and `c(2,q) = 1 - q`. Then `X` acts on `L` by `c ↦ c - 1`, and
by uniform depth `b` acts by `c ↦ c + t` whenever `|c| >= ℓ + 3`. By bounded
displacement, `|t| <= ℓ`. So `σ = b X^t` fixes ray 3 and every `c` with
`|c| >= ℓ + 3`, and it permutes the interval
`I = {-(ℓ+2), ..., ℓ+2}`, which has `N = 2ℓ + 5` points.

**Bubble sort.** For `c ∈ Z` let `s_c` swap the `L`-points `c` and `c+1`.
Then `s_c = X^(c-1) α X^(1-c)`. Bubble sort writes every permutation of `I`
as a product of at most `N - 1` passes. A pass is `s_(c_1) s_(c_2) ... s_(c_r)`
with `c_1 < ... < c_r` in `I`, and it equals the word

`X^(c_1 - 1) α X^(c_1 - c_2) α X^(c_2 - c_3) ... α X^(1 - c_r)`,

which has length at most `r + |c_1 - 1| + (c_r - c_1) + |1 - c_r| <= 4N`. So
`|σ|_(S_2) <= 4N(N-1)`, and `b = σ X^(-t)` gives

`|b|_(S_2) <= 4N^2 + ℓ = 4(2ℓ+5)^2 + ℓ`.

In particular every element of the stabilizer `B_2` is a word in `X, α`. ∎

## Part (a), lower bound

`inv(h)` counts the pairs `y < y'` of `L` with `yh > y'h`. It is subadditive,
because an inversion of `gh` is an inversion of `g`, or else the image under
`g` of an inversion of `h`. Also `inv(X^(±1)) = 0` and `inv(α) = 1`. So
`|h|_(S_2) >= inv(h)`.

For `h = h_(m-1) = Y^(m-1) X^(-m) Y^(-(m-1))`: it fixes `(1,1), ..., (1,m-1)`.
It sends `(2,q)` for `q <= m` to ray 1 at depth `> m-1`, and it is an
order-preserving shift of `L` elsewhere. So `inv(h) = m(m-1)`. This is (F2) of
`houghton-h3-at-least-cubic-dehn-corridor-proof`, and it was recomputed
independently in `referee_and_cap.out`. Also `|h|_S <= 3m - 2`. This is the
quadratic distortion that BCMR (arXiv:1403.0026, Theorem 5.1: "The group H2 is
at least quadratically distorted in Hm for m ≥ 3") prove with a different
family. ∎

**Machine sanity check.** `referee_and_cap.py` builds the bubble-sort word for
random elements `Y^a u Y^(-a)` of `B_2` and for `h_k`. It verifies each word
as a permutation and reports `|word| / ℓ^2 <= 0.32` for `ℓ <= 32`.
