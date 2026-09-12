---
rg: 2
id: anti-central-rank-functions-give-weakly-finite-leavitt-images
kind: claim
title: A rank function on the ternary anti-central summand gives a weakly finite image into whose units the Leavitt unit group embeds
distinct_from:
  ternary-anti-central-states-force-nontrivial-rank-models: that is the open upgrade from states to rank models; this is the established necessary condition that any rank function on the summand already forces a nonzero weakly finite image carrying the whole unit group.
  ternary-leavitt-rank-models-move-z-iff-nontrivial: that compares rank models of the unit group and its scalar quotient; this starts from an abstract Sylvester rank function on the anti-central summand, not a matrix model.
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

**ESTABLISHED** (artifact Corollary A.2). Let `G_3 = L_(F_3)(1,2)^x`, `z = -1`, and
`S_- = eps_- F_3[G_3]`. Suppose `N` is a Sylvester matrix rank function on `S_-` with `N(eps_-) = 1`.
Put `Q = S_- / ker N`. Then:
1. `Q` is a nonzero weakly finite `F_3`-algebra with a faithful rank function;
2. `rk(X) = N(X eps_-)` is a Sylvester matrix rank function on `F_3[G_3]` with `rk(1 - [g]) > 0` for
   every `g != 1`;
3. `g -> [g] eps_- + ker N` embeds `G_3` into `Q^x` and sends `z` to `-1`.

**Consequence for the state upgrade.** Step (U1) of `ternary-anti-central-states-force-nontrivial-rank-models`
(a state gives a rank function) implies (U1a) `anti-central-rank-condition-gives-weakly-finite-image`. So
any proof of (U1) must produce a proper ideal of `S_-` with a nonzero weakly finite quotient, unless
`S_-` is itself stably finite.

Proof: route `anti-central-rank-functions-weakly-finite-image-proof`.
