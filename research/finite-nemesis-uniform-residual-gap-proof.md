---
rg: 2
id: finite-nemesis-uniform-residual-gap-proof
kind: route
title: Use lower semicontinuity and a finite positive subcover
target: finite-nemesis-subcover-has-a-uniform-existential-residual-gap
requires:
  - bespoke-extension-nemesis-library-defeats-diagonal-schedules
---

For fixed `i`, the continuous-logic formula `inf_y G_i(x,y)` is uniformly
continuous in `x`; its restriction to the compact matricial type subspace is
`rho_i`.  Alternatively, compact projection of `G_i<=c` proves the weaker
lower semicontinuity already sufficient below.  If `rho_i(x)>0`, the
open set `{rho_i>rho_i(x)/2}` contains `x`.  Exhaustiveness makes these sets,
over all `x` and their chosen gadgets, an open cover of `K_alpha`.  Choose a
finite subcover and take the minimum of its finitely many positive half-gaps;
this proves `(FER3)`.

If no finite matrix tolerance realized `epsilon/2`, choose increasingly
accurate counterexamples and take their ultraproduct.  The base marginal lies
in `K_alpha`, while every selected gadget has residual below `epsilon/2`,
contradicting `(FER3)`.
