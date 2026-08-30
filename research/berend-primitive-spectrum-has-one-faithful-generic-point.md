---
rg: 2
id: berend-primitive-spectrum-has-one-faithful-generic-point
kind: claim
title: The Berend primitive spectrum has one faithful generic point and only finite-dimensional closed points
distinct_from:
  berend-proper-quotients-have-decomposition-rank-at-most-two: that controls arbitrary proper quotients; this identifies all primitive quotients and the unique dense point of the primitive spectrum.
  berend-finite-orbit-quotients-are-asymptotically-isometric: that is a norm approximation by growing finite-orbit quotients; this is the exact primitive-representation stratification underlying those quotients.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `A = C(T^3) ⋊ Z^2` be the Berend crossed product.  Then `0` is a
primitive ideal and is the unique dense point of `Prim(A)`.  Every other
primitive ideal is maximal and its irreducible quotient is a matrix
algebra.

More precisely, set-theoretically,

`Prim(A) \ {0} = disjoint_union_O dual(Stab(O))`,               `(BPS1)`

where `O` ranges over the finite Berend orbits.  Each stabilizer has finite
index in `Z^2`, so every summand in `(BPS1)` is a two-torus, and its points
are kernels of irreducible representations of dimension `|O|`.  Each such
torus is a closed subset of `Prim(A)`; the full topology also records their
accumulation toward the dense point `0`.

Consequently no primitive quotient, and no single closed primitive
stratum, can witness infinite decomposition rank.  Any primitive-spectrum
obstruction for the full algebra must use the global accumulation of these
finite-dimensional strata at the faithful generic representation.
