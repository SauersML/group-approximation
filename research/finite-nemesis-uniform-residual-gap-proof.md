---
rg: 2
id: finite-nemesis-uniform-residual-gap-proof
kind: route
title: Use lower semicontinuity and a finite positive subcover
target: finite-nemesis-subcover-has-a-uniform-existential-residual-gap
requires:
  - bespoke-extension-nemesis-library-defeats-diagonal-schedules
---

For fixed `i` and `c`, intersect the compact joint matricial type space with
the closed condition `G_i<=c` and project to the base coordinates.  Its image
is compact, proving lower semicontinuity of `rho_i`.  If `rho_i(x)>0`, the
open set `{rho_i>rho_i(x)/2}` contains `x`.  Exhaustiveness makes these sets,
over all `x` and their chosen gadgets, an open cover of `K_alpha`.  Choose a
finite subcover and take the minimum of its finitely many positive half-gaps;
this proves `(FER3)`.

If no finite matrix tolerance realized `epsilon/2`, choose increasingly
accurate counterexamples and take their ultraproduct.  The base marginal lies
in `K_alpha`, while every selected gadget has residual below `epsilon/2`,
contradicting `(FER3)`.

