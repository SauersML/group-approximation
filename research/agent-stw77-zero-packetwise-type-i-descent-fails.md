---
rg: 2
id: agent-stw77-zero-packetwise-type-i-descent-fails
kind: claim
title: Packetwise type-I absorption supplies no operator-norm descent
distinct_from:
  agent-stw77-zero-type-i-weak-closure-obstruction: that blocks two weak-closure shortcuts by von Neumann type; this gives an operator-norm gap even in a faithful irreducible type-I representation.
  agent-stw77-zero-type-i-proper-support-models: that constructs proper-support models in the represented type-I target; this shows those models need not be near-included in the original C-star algebra.
---

There are a separable unital properly infinite C-star algebra `B`, a faithful
essential representation

```text
pi:B->B(H),
```

a nuclear-dimension-zero proper-image map `phi:C->B`, a unital
finite-dimensional algebra `D subset B`, and a type-I absorbed copy

```text
rho:D->B(H)
```

with the following properties.

1. Every minimal projection of `rho(D)` is properly infinite in `B(H)`.
2. `rho(D)` contains `(pi compose phi)(C)`, so its approximation error on
   the entire range is zero.
3. For one minimal projection `q in rho(D)`,

   ```text
   dist(q,pi(B))>=1/3.
   ```

In particular `rho(D)` is not even one-sided Kadison--Kastler near-included
in `pi(B)` with constant below `1/3`, and no homomorphism
`theta:rho(D)->pi(B)` can be within `1/3` of the inclusion on the unit ball.

Consequently finite-packet closeness of an absorbed proper-support model to
the represented range gives none of the unit-ball near-inclusion required by
finite-dimensional perturbation theorems.  Any operator-norm descent route
for `stw77-nucdim-zero-case` must select the absorbing unitary using
additional global information about the model algebra; arbitrary measurable
Voiculescu absorption cannot be descended.
