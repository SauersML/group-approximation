---
rg: 2
id: fpbs-gap-survives-product-generator-moves
kind: claim
title: Adding or removing one product generator never closes the percolation threshold gap
distinct_from:
  fpbs-nonuniqueness-phase-is-a-group-invariant: that compares arbitrary generating sets; this concerns one elementary move at a time, and with fpbs-generating-sets-connected-by-product-moves it is equivalent to that claim.
  fpbs-generating-set-threshold-comparison: that proves threshold inequalities with a power loss; this asserts the loss never closes a gap under a single move.
artifacts:
  - research/artifacts/fpbs-choi-seo-q12-invariance-2026-09-12.md
---

**OPEN.** Let `Gamma` be a finitely generated group, and let `S` be a finite
symmetric generating set not containing `e` with
`p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`. Then both kinds of move preserve the
gap:

- **Add.** For `t = uv` with `u, v in S` and `t ∉ S ∪ {e}`, the set
  `S ∪ {t, t^{-1}}` has `p_c < p_u`.
- **Remove.** For `t in S` with `t = uv`, `u, v in S \ {t, t^{-1}}`, the set
  `S \ {t, t^{-1}}` has `p_c < p_u`.

By `fpbs-generating-sets-connected-by-product-moves`, this implies Choi--Seo
Question 1.2 (`fpbs-nonuniqueness-phase-is-a-group-invariant`). Conversely, it
is a special case of that claim.

## Attempts

* **Threshold comparison with a power map.**
  `fpbs-generating-set-threshold-comparison` gives, for one Add move from `G` to
  `G⁺` (words of length `L = 2`, multiplicity `M`, map `phi`):
  - `phi(p_c(G)) <= p_c(G⁺) <= p_c(G)`;
  - `phi(p_u(G)) <= p_u(G⁺) <= p_u(G)`.

  So the gap survives whenever `p_c(G) < phi(p_u(G))`, which is about
  `p_c(G) < p_u(G)^2/4` in the generic case. Symmetrically, a Remove move keeps
  the gap whenever `phi^{-1}(p_c(G⁺)) < p_u(G⁺)`.

  **Where it dies:** when the two windows overlap. A counterexample must be an
  Add move that pushes `p_u` down to `p_c`, or a Remove move that pushes `p_c`
  up to `p_u`, inside those windows.
* **Lossless comparison through connection events.** Using `x <-> xt` in the
  old configuration as the comparison event for a new edge `{x, xt}` would lose
  nothing.

  **Where it dies:** those events are dependent across new edges. Turning a
  dependent comparison process into a threshold statement needs uniqueness
  monotonicity for that process, and the imports available on main give
  monotonicity only for Bernoulli percolation.
* **Relative gap along a subgroup** (`fpbs-relative-gap-along-any-subgroup-separates`).
  The comparison transfers finiteness of relative susceptibility only at the
  distorted parameter.

  **Where it dies:** same margin as above, since the criterion transfers from
  `G` to `G'` only if `p_c(G') < phi(p)`.

Details in Section 4 of the artifact.
