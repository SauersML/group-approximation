---
rg: 2
id: bernoulli-isomorphism-collapse-set-is-a-subgroup-proof
kind: route
title: Multiply isomorphisms by Bernoulli factors, chain witnesses upward, and read the constraints on counterexample groups
target: bernoulli-isomorphism-collapse-set-is-a-subgroup
requires:
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - bernoulli-entropy-counterexample-constraints
---

"Theorem 1.1" is the import in the first prerequisite. "Part (x)" refers to the
second prerequisite.

**Item 1.** `(L^G, λ^G) × (M^G, μ^G)` with the diagonal action is the Bernoulli shift
`((L × M)^G, (λ × μ)^G)`, and `H(λ × μ) = H(λ) + H(μ)`, also when one side is
infinite. Theorem 1.1 then gives `X_a × X_b ≅ X_(a+b)`. If `φ: X_h → X_(h')` is an
isomorphism, `φ × id` is an isomorphism `X_h × X_t → X_(h') × X_t`.

**Item 2.** Item 1 with `t` turns `X_h ≅ X_(h+d)` into `X_(h+t) ≅ X_(h+t+d)`, and
`h + t + d ≥ h + d ≥ 0`.

**Item 3.**
- `0 ∈ D(G)`, with witness `h = 0`.
- If `h ∈ W_d`, then `h + d ∈ W_(−d)`, because `X_(h+d) ≅ X_h`, `h + d ≥ 0` and
  `(h + d) − d ≥ 0`. So `D(G) = −D(G)`.
- Let `h ∈ W_d` and `k ∈ W_e`, and put `p = max(h, k − d)`. By item 2, `p ∈ W_d`, so
  `X_p ≅ X_(p+d)` and `p + d ≥ 0`. Also `p + d ≥ k`, so `p + d ∈ W_e` by item 2, and
  `X_(p+d) ≅ X_(p+d+e)` with `p + d + e ≥ 0`. Chaining, `p ∈ W_(d+e)`.

**Item 4.** If `0 ≠ d ∈ D(G)` with `h ∈ W_d`, then `X_h ≅ X_(h+d)` is a failure of
classification. Conversely, suppose `X_(h_1) ≅ X_(h_2)` with `h_1 < h_2`. Part (b)
gives `0 < h_1 < ∞`.
- If `h_2 < ∞`, then `h_2 − h_1 ∈ D(G)`.
- If `h_2 = ∞`, item 5 gives `D(G) = R`.

For the absorption form, `X_h × X_d ≅ X_(h+d)` by item 1. If `d < 0` is in `D(G)`,
use `−d` and the witness `h + d`, which is positive by part (b).

**Item 5.** For `h' ≥ h`, item 1 and Theorem 1.1 for infinite bases give
`X_(h') ≅ X_h × X_(h'−h) ≅ X_∞ × X_(h'−h) ≅ X_∞`. For `d ∈ R` put `p = h + |d|`. Then
`p + d ≥ h`, and `X_p ≅ X_∞ ≅ X_(p+d)`, so `d ∈ D(G)`. Part (c) gives
`h^Rok_sup(G) = 0`.

**Item 6.** The bound is part (b) applied to the pair `min(h, h + d) < max(h, h + d)`.
For periodicity:
- For each `i` pick `w_i ∈ W_(d_i)`, and put `θ = max_i (w_i + |d_i|)`.
- Let `p ≥ θ`. Then `p ≥ w_i`, so `X_p ≅ X_(p+d_i)` by item 2.
- Also `p − d_i ≥ w_i`, so `X_(p−d_i) ≅ X_p`.
- So from any point `p ≥ θ`, a step of `±d_i` preserves the isomorphism class.

Write `h' − h = Σ_i n_i d_i` with integers `n_i`. Take all steps that increase entropy
first and then all steps that decrease it. Every intermediate point is then at least
`min(h, h') ≥ θ`.

**Item 7.** This is part (d): an isomorphism over `G` co-induces to one over `G'` with
the same bases, and restricts to a subgroup of index `k` with base entropies
multiplied by `k`. A witness `h` for `d` becomes the witness `h` over `G'`, and `k·h`
for `k·d` over `H`.

**Item 8.** If `0 ≠ d ∈ D(G)`, item 6 gives `h^Rok_sup(G) ≤ min(h, h + d) < ∞`. So the
dichotomy leaves `h^Rok_sup(G) = 0`.

**Sofic groups.** Part (a) gives `D(G) = {0}`.
