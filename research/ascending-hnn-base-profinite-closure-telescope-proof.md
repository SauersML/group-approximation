---
rg: 2
id: ascending-hnn-base-profinite-closure-telescope-proof
kind: route
title: Finite quotients force equal level images, while height quotients exclude everything outside the telescope
target: ascending-hnn-base-profinite-closure-telescope
requires: []
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
---

## Complete proof

Let `L<=V` be finite index with `Gamma<=L`, take its finite-index normal core
`C`, and write `q:V->V/C`.  In the finite target,

`q(t) q(Gamma) q(t)^-1 = q(alpha(Gamma)) <= q(Gamma)`.

The two finite groups on the left and right of the inclusion have equal
cardinality because conjugation is bijective, so equality holds.  Iterating
shows `q(t^-r Gamma t^r)=q(Gamma)` for every `r`.  Since `C<=L`, every level is
contained in `L`; hence the telescope kernel `N` lies in every finite-index
overgroup of the base.

Conversely, if `x` is outside `N`, its height in `Z` is nonzero.  Reducing the
height modulo an integer not dividing that value gives a finite-index subgroup
containing `Gamma` but excluding `x`.  Thus the profinite closure is exactly
`N`.
