---
rg: 2
id: semicontinuous-invariants-blind-above-rokhlin-supremum-proof
kind: route
title: Two-sided weak* approximation by isomorphic shift models forces a semicontinuous invariant to agree
target: semicontinuous-invariants-blind-above-rokhlin-supremum
requires:
  - rokhlin-entropy-is-the-bernoulli-approximation-threshold
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
---

Every `h ∈ (0, ∞)` is the entropy of a finite base, so `I(h)` is defined for all such
`h`. Fix `0 < a < b < ∞` and finite bases `(K, κ)` and `(L, λ)` with `H(κ) = a` and
`H(λ) = b`. "The Corollary" is the approximate classification in the first
prerequisite.

**Item 1.** `min(a, s) ≤ a < b`, so the Corollary gives `ν_n ∈ M_L(K^G)` with
`ν_n → λ^G`. Each `G ↷ (L^G, ν_n)` is isomorphic to `K^G`, so
`I(L^G, ν_n) = I(a)`. Upper semicontinuity at `λ^G` gives

    I(b) = I(L^G, λ^G) ≥ limsup_n I(L^G, ν_n) = I(a).

**Item 2.** Suppose also `s < a`. Then `min(b, s) = s < a`, so the Corollary with the
two bases exchanged gives `μ_n ∈ M_K(L^G)` with `μ_n → κ^G`. Upper semicontinuity at
`κ^G` gives `I(a) ≥ I(b)`. With item 1, `I(a) = I(b)`.

**Lower semicontinuous `I`.** The same sequences give `I(b) ≤ I(a)` in item 1 and
`I(a) ≤ I(b)` in item 2.
