---
rg: 2
id: orientation-lift-selectors-need-vanishing-host-gap
kind: claim
title: A polynomial-time branch selector whose YES orientation lifts have value 1 - eta' on 2-to-1 hosts with lambda_2 >= X(delta) eta' puts its source in P, so every selector route to UGC needs host spectral gaps vanishing at least linearly in the lift error
distinct_from:
  efficient-branch-selectors-list-decode-honest-outer-labels: that kills selectors whose lift witnesses are honest encodings, by list decoding, conditional on NP not in RP; this kills every selector and every witness, honest or not, by the spectral gap of the host alone, conditional on P != NP, and says nothing on hosts with small gap.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that needs witnesses near locally honest patchworks; this needs no structure of the witness at all, so it also covers the non-rigid survivor (H2-loc), but only on hosts whose gap beats X(delta) eta'.
  view-local-branch-selectors-are-gauge-blind: that bounds honest completeness of bounded-view selectors by gauge symmetry; this has no view hypothesis.
  spectral-gap-ratio-reductions-cannot-prove-ugc: that gates unique-games reductions with regular YES outputs; this applies the gate to orientation lifts, whose hosts are bipartite and in general irregular, through the degree blow-up.
  degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts: that is the general gate on loop-free irregular hosts; this is its specialization to orientation lifts, with soundness supplied by the sandwich.
---

**ESTABLISHED.** Route: `orientation-lift-host-gap-proof`.

## Statement

Fix `delta < 1`, and let `X(delta)` be the constant of gate (K1) (the least
integer `x >= 3` with `C_A log(x)/x < 1 − delta`). Let

* `R` be a polynomial-time map from strings to weighted bipartite 2-to-1 games
  `G(x)` (setting of `orientation-lifts-sandwich-2to1-game-values`) with integer
  multiplicities of total `W(G(x)) <= poly(|x|)`;
* `S` be a polynomial-time map sending `x` to an orientation `o = S(x)` of
  `G(x)`, with lift `U_o(x)`;
* `eta' in [0, 1)` a constant.

Suppose that for a language `L`:

* `x in L` implies `val(U_(S(x))) >= 1 − eta'`, `λ_2(G(x)) > 0` and
  `min(λ_2(G(x)), 1) >= X(delta) eta'`;
* `x notin L` implies `val(G(x)) <= delta`.

Then `L in P`. Here `λ_2(G)` is the second normalized-Laplacian eigenvalue of
the weighted constraint graph of `G`; it is a property of the host alone, the
same for `G` and for every orientation lift.

**Corollary (necessary shape of every selector route).** Assume `P != NP`, and
let `(R_eta, S_eta)` be reductions and selectors from an NP-hard gap-3LIN source
realizing `parity-leaking-branch-selectors-reach-near-perfect-completeness` (or
`efficient-branch-selector-on-proved-2to1-instances`) at soundness `delta` with
lift error `eta'(eta) → 0`. Then for every small `eta` some YES input `x` has

```text
λ_2(G_eta(x)) < X(delta) · eta'(eta).
```

So the YES hosts' spectral gap must tend to `0` at least linearly in the lift
error. A fixed family of hosts with gap bounded below kills the route outright,
whatever the selector reads and whatever the witness looks like.

## Where every member dies

At the YES lift, before soundness is used: the lift is a unique game of value
`1 − eta'` on a host of gap `λ_2 >= X(delta) eta'`, and AKKSTV rounding (after
the degree blow-up) finds a labelling of value `> delta`, which no NO lift has.
The invariant is `λ_2(host) / eta'`.

## What it changes on the selector decomposition

* The parity-leaking node now carries a second necessary condition, independent
  of the gauge one of `view-local-branch-selectors-are-gauge-blind`: the
  reduction must supply hosts whose gap vanishes with `eta'`. For the DKKMS
  shape, the per-`U` Grassmann layer does not provide this, since its
  containment walk has constant gap. So the vanishing gap must come from the
  outer `U -> V -> U'` smoothing walk: from the smoothing parameter `beta`, or
  from the expansion of the 3LIN source.
* **Open (need posted).** Lower-bound `λ_2` of the folded DKKMS constraint graph
  by a function of `(beta, k, l)` times the gap of the source's
  equation-variable walk. If that bound holds and the parameters DKKMS fix for
  soundness `delta` keep `beta` and the source gap bounded below as `eta → 0`,
  this claim kills `efficient-branch-selector-on-proved-2to1-instances` under
  `P != NP` alone. That would bypass the open rigidity question
  `dkkms-grassmann-2to1-test-is-locally-99-percent-rigid` entirely.
* **Not covered.** Moderate completeness: the gate needs `1 − c <= λ_2 / X(delta)
  <= 1/3`, so selectors with YES lift value `c` just above `1/2` are untouched.
  Hosts with loops, and hosts given with superpolynomial binary weights, are also
  outside, as in the blow-up node.

This neither proves nor refutes UGC.
