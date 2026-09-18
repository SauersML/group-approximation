---
rg: 2
id: orientation-lift-host-gap-proof
kind: route
title: Feed the orientation lift, which lives on the same loop-free bipartite host, into the blow-up gate, with soundness from the sandwich
target: orientation-lift-selectors-need-vanishing-host-gap
requires: [degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts, orientation-lifts-sandwich-2to1-game-values]
---

Notation is that of the target.

**The reduction.** Put `f(x) := U_(S(x))(G(x))`. It is computed in polynomial
time from `R` and `S`: the lift replaces each 2-to-1 projection `p_e` by the
bijection `a -> (p_e(a), o_e(a))` (setting of
`orientation-lifts-sandwich-2to1-game-values`), one table per edge.

**Host.** By that setting, `U_o` is the unique game "on the same weighted
graph" as `G`. So `f(x)` has the constraint graph of `G(x)`: the same
multiplicities, total `W <= poly(|x|)`, and the same `λ_2`. It is bipartite,
so it has no loops.

**YES.** If `x in L`: `opt(f(x)) >= val(U_(S(x))) >= 1 − eta'`, so
`X(delta)(1 − opt(f(x))) <= X(delta) eta' <= min(λ_2(f(x)), 1)`, and
`λ_2(f(x)) = λ_2(G(x)) > 0`.

**NO.** If `x notin L`: by item 1 (Sandwich) of the lift node,
`opt(f(x)) <= val(G(x)) <= delta`.

These are the hypotheses of Theorem 2 of
`degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts` with `s = delta`.
So `L in P`.

**Corollary.** If for some small `eta` every YES input had
`λ_2(G_eta(x)) >= X(delta) eta'(eta)` (hence `min(λ_2, 1) >= X(delta) eta'`
whenever `X(delta) eta' <= 1`, which holds once `eta' <= 1/3`), then the NP-hard
source language would be in P.
