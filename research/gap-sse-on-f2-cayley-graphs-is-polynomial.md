---
rg: 2
id: gap-sse-on-f2-cayley-graphs-is-polynomial
kind: claim
title: There is an absolute eta_0 > 0 such that for every dyadic delta, Gap-SSE(eta_0, delta) on weighted Cayley graphs of F_2^k given by their weight table is decidable in time N^(log2(1/delta) + O(1)), so no SSEH reduction can output F_2^k Cayley graphs (unless P = NP)
distinct_from:
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that proves the same algorithm correct only for eta below 2/(log2(1/delta) + 3.61), which shrinks with delta; this asks for one eta_0 at all measures.
  small-set-expansion-hypothesis: that asserts hardness on general graphs for every eta at some delta; this asserts easiness on one graph class at a fixed eta_0 for every delta, and so restricts the output class of any reduction proving it.
---

**OPEN.** Input: `k`, a dyadic measure `delta = 2^(-c)`, and weights
`w : F_2^k \ {0} -> Q_(>= 0)` (the table has `N = 2^k` entries). Decide whether
`Phi_G(delta) <= eta_0` or `Phi_G(delta) >= 1 - eta_0` for
`G = Cay(F_2^k, w)`, under the promise that one holds.

Route: `f2-cayley-gap-sse-by-subgroup-enumeration`. It requires
`f2-cayley-subgroup-sets-are-constant-factor-optimal`, and its argument uses only
that claim's weak form.

*Consequence for SSEH.* Say a reduction outputs `F_2^k` Cayley graphs if, on
every NO instance, it outputs a weight table on `F_2^k` whose Cayley graph is
the output graph. For `eta < eta_0` and any `delta`, such a reduction to
`Gap-SSE(eta, delta)` composed with the algorithm puts its source language in
`P`. This is the abelian-Cayley survivor "abelian Cayley (rank n^Omega(1))" of
the live-bus lemma `sse-reductions-need-high-threshold-rank-on-both-sides`.
Recognising a hidden Cayley structure in a graph given only by adjacency is not
addressed.

*Shrinking-eta part, not yet established.* A drafted but unrefereed argument
gives the algorithm for `eta < 2/(log_2(1/delta) + 3.61)`
(`f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`, item 3, itself OPEN
because its proof has had no referee pass). Even granting it, the range shrinks
with `delta`, so it does not give the fixed `eta_0` asked for here.

## Attempts

* **Subgroup enumeration with the proved log-loss (2026-09-17, swarm-0917).**
  - *Result.* The enumeration is correct for `eta (c + 3.61) < 2`.
  - *Where it dies.* At fixed `eta` it stops at `delta = 2^-(2/eta - 3.61)`,
    which is exactly the SSEH regime. A constant subgroup-dominance factor
    (`f2-cayley-subgroup-sets-are-constant-factor-optimal`) is what is missing.
* **Basic SDP (Delsarte LP) as the decision procedure.**
  - *Where it dies.* The SDP is not the obstacle on these instances. In the
    census it overshoots by at most `0.015` at `s = 8`
    (`f2-cayley-sse-exact-census-small-k`). But a tight general bound would itself
    refute SSEH on this class only through a rounding, and the only rounding known
    here is the subgroup one above.
