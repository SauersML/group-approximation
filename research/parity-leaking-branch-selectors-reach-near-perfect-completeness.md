---
rg: 2
id: parity-leaking-branch-selectors-reach-near-perfect-completeness
kind: claim
title: Some polynomial-time branch selector with global, parity-leaking views orients the Grassmann 2-to-1 instances of a gap-3LIN source so that YES orientation lifts have value at least 1 - eta' while NO lifts keep value at most delta
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that kills selectors whose views are parity-faithful; this is the surviving global case, and the kill supplies its necessary condition (parity leakage on a 1 - 2 eta' - o(1) fraction of edges).
  unique-games-hard-at-completeness-one-half: that reaches completeness 1/2 obliviously by splitting; this asks for a computed, instance-dependent orientation above 1/2.
---

**OPEN.** This is heretic denial H1.

**Assumption denied (A1).** The HOT families (local-designs, probability-random)
assume hardness is generated edge-locally. Each constraint's accept set is fixed
by a local gadget, such as a long-code or noise test, a local wrapper or a pairing
design, and completeness is oblivious. Every recorded kill of that class
(`unique-constraints-orient-at-most-half-of-a-fiber`,
`grassmann-composed-2to2-coarsenings-are-satisfiable`,
`linear-view-unique-verifiers-collapse-to-quotient-coarsening`) stops at the
one-half wall. The denial is that the branch choice is computed from the whole
instance.

**Claim.** There are a polynomial-time reduction from a gap-3LIN problem to
Grassmann 2-to-1 instances `D(I)` (the DKKMS shape) and a polynomial-time selector
`S` with the following two properties:
- on YES inputs, `val(U_(S(I))) >= 1 - eta'(eta)` with `eta' -> 0`;
- on NO inputs, `val(D(I)) <= delta`.

Every lifted constraint implies the source constraint, so `val(U_o) <= val(G)`
and the NO bound transfers to the lift. This claim therefore implies UGC, through
`ugc-via-parity-leaking-branch-selector`. Worker e-ugc-2to1-reframe also reports
that the right merge of the lift is fully rich, which would give the Rich 2-to-1
form directly. The weaker version with any
constant `c > 1/2` in place of `1 - eta'` would already beat the one-half wall of
`unique-games-hard-at-completeness-one-half`.

**Established necessary condition.** By `view-local-branch-selectors-are-gauge-blind`,
any `S` whose certificate is an honest labelling from an equivariant menu of size
`exp(o(n/s^2))` must have parity leakage `w_bad >= 1 - 2 eta' - o(1)`. On almost every
edge its view must span a parity of window variables outside `H_U`, so it must see
a cycle of equations through the window.

**Falsifiers.**
- (i) Show that a selector as claimed, together with its honest certificate,
  yields a polynomial-time algorithm that beats `1/2 + eps` on the gap-3LIN
  source. That would refute the claim under P != NP.
- (ii) Show that for every selector the lift value is at most
  `1/2 + w_bad/2 + o(1)` on most gauges, for all labellings and not only honest
  ones. Then completeness `1 - eta'` forces `w_bad -> 1`. Combined with (i),
  that closes the case.

## Attempts

* **Bounded parity-faithful views (2026-09-18).** **Dead.** Killed by
  `view-local-branch-selectors-are-gauge-blind`: under the gauge `z`, the branch
  bit is exactly uniform given the view, so honest completeness is at most
  `1/2 + w_bad/2` over subexponential equivariant menus. Only global views,
  unclustered menus or non-honest certificates survive.
* **Near-perfect selectors on DKKMS-form instances in the covering regime
  (2026-09-18).** **Dead under NP not in RP.** Killed by
  `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`. When `D(I)` is
  the DKKMS construction, after any polynomial-time 3LIN map, at `(l,k)` with
  `SD* <= 10^(-5)` and Corollary-A admissibility, a selector with any views,
  global or parity-leaking, with or without a certificate, and YES lift value
  `>= 1 - 10^(-5)` puts the source in RP. Falsifier (i) is realised at
  completeness `1 - 10^(-5)` for every selector, not only honest ones. For
  advice dimension `q >= 2` the regime is every admissible point with `l >= 43`.
  Survivors: completeness in `(1/2, 1 - 10^(-5))`; `q = 1` with
  `k_A(l) <= k < k_0(l)`; non-DKKMS `D(I)` (another inner test or outer game).
  The claim stays OPEN for those.
* **Spectral-gap gate on the host (2026-09-18).** **Conditional kill, OPEN.**
  - *What is proved.* Gate (G) of
    `akkstv-rounding-holds-on-all-loop-free-constraint-graphs` is
    ESTABLISHED. On any YES host family with `λ_2 >= X(δ) η'`, a polynomial-time
    selector with lift value `1 − η'` puts the source in P. This holds whatever
    the views or certificates are.
  - *Where the gate lands on DKKMS.* The unfolded DKKMS host has gap `Θ(β)`,
    and `β −> 0`. But the folded host measured in
    `folded-dkkms-hosts-keep-spectral-gap-as-smoothing-vanishes` keeps a gap
    near `1 − sqrt(1 − 4^(−l))` even at `β = 0`, because folding resamples the
    free blocks.
  - *What this gives.* If that OPEN claim holds, this node is false on the
    DKKMS shape under P != NP alone: `η' >= c(l)/X(δ)` with `l = l(δ)`.
  - *Where H1 can still live.* Only on reductions whose folded YES host gap
    tends to 0, or through a failure of (P1)–(P5) there.
