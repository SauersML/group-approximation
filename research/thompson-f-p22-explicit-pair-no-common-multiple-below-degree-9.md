---
rg: 2
id: thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9
kind: claim
title: An explicit integer pair in Guba's Problem P_(2,2) for Thompson's F has no nonzero common right multiple of degree at most eight
distinct_from:
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the cardinality ratio of S_(3,5) exactly and finds no certificate up to degree 12; this is a linear-algebra lower bound for one explicit pair, valid for every method of finding a common multiple, and says nothing about cardinality.
  thompson-f-p21-cardinality-certificate-in-degree-eleven: that solves every pair of P_(2,1) in degree eleven; this shows that a pair of P_(2,2) needs degree at least nine, and solves nothing.
  thompson-f-amenable-iff-group-ring-is-ore: that turns amenability into the Ore condition; this bounds the degree of any Ore solution for one pair of degree-two elements.
artifacts:
  - research/artifacts/hl-thompson-f-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof` (exact computation over
`F_p`, `p = 2^61 - 1`, with a deterministic certificate; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F` and `S = S_(3,5)` the nine monomials of Guba's Problem `P_(2,2)`,
in the order `x_0^2, x_0x_1, x_0x_2, x_0x_3, x_1^2, x_1x_2, x_1x_3, x_2^2, x_2x_3`. Let `a = Σ α_s s` and
`b = Σ β_s s` in `Z[S]`, with integer coefficients in that order:

- `α = 1879332192264247163, 713376164582626380, 16889165297986115, 1424372661569722877,
  1809193355447410310, 75245988799813482, 343606203294106168, 319599478854802929, 1019030692220978450`;
- `β = 741092729165237384, 480484019229034295, 480784405906419460, 2005441565472458781,
  1839560932147697539, 2127126162642565001, 2040254807131644771, 428606865701911994, 1311528060322210779`.

**Claim.** Let `K` be a field of characteristic `0`, or a field containing `F_p`. If `u, v ∈ K[M]` have
all their terms of degree `<= 8` and `a u = b v`, then `u = v = 0`.

**Consequences.**
- In characteristic `0`, the pairs `(a, b) ∈ K[S]^2` that have a nonzero common right multiple of degree
  `<= 8` form a proper Zariski-closed subset of `K^18`. A generic pair of `P_(2,2)` needs degree at least 9.
- For comparison, the cardinality method needs degree at least 13 for `S_(3,5)`:
  `Λ(12) ≈ 2.6676` in `thompson-f-monomial-doubling-ratio-is-a-finite-computation`.
- Guba's survey (arXiv:2305.07113v4, l.663–665) lists `P_(2,2)` as the first unknown case. This lower
  bound does not decide it.

**Scope.** This proves no solvability and no non-solvability of `P_(2,2)`. It covers one explicit pair,
fields of characteristic 0 and fields containing `F_(2^61-1)`, and degrees `<= 8`.
