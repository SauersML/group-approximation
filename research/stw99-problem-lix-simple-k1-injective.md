---
rg: 2
id: stw99-problem-lix-simple-k1-injective
kind: claim
title: Unital simple C*-algebras are K1-injective (STW Problem LIX)
root: true
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: that asks K1-injectivity from proper infiniteness without simplicity; this asks it from simplicity without any regularity, and Villadsen's Crelle examples already kill the surjectivity analogue here.
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
---

**Problem LIX of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Are
all unital simple C\*-algebras `K_1`-injective?  Villadsen (Crelle,
Thm 12) killed `K_1`-SURJECTIVITY for simple algebras with arbitrarily
long failure windows `π_k(U_n) → π_k(U_{n+1})` non-surjective for
`n ≤ n_0`; injectivity is open.

## Attempts

* Villadsen's mechanism produces unitaries NOT reachable from the
  first matrix level (Euler-class sections missing), which is
  precisely a surjectivity obstruction; an injectivity failure needs
  the opposite: a unitary trivial in `K_1` but not null-homotopic in
  `U(A)` — over commutative base this is a nontrivial element of
  `π_1`-type odd cohomology killed by stabilization, e.g. the
  suspension phenomena on spheres (`U(n)`-bundles with vanishing
  stable class but nonzero unstable obstruction in
  `π_{2k}(U(n))`-torsion).  Those unstable homotopy obstructions ARE
  available in the Villadsen calculus (odd-degree analogues of the
  session's mod-`ell` Chern thresholds: finite-order elements of
  `π_{2n}(U(n))` pulled through coordinate embeddings), and nothing in
  the seed-duplication maps obviously kills torsion classes the way
  rank growth kills the stable ones.  Recorded as the concrete
  candidate: a Villadsen-type limit engineered so a `π_{2n}(U(n))`
  torsion class survives all connecting maps while its `K_1` class
  dies — the first non-stable-homotopy computation of this shape;
  no result in the literature blocks it.
