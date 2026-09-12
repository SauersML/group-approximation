---
rg: 2
id: smooth-label-cover-projective-color-proof
kind: route
title: Partition each smooth-label edge by its common projection value
target: smooth-label-cover-edges-are-finite-phase-projective-color
requires:
  - monomial-game-pair-compatibility-is-projective-color-rigid
artifacts:
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
---

Definition 3 of Culf--Mastel--Paddock--Spirig,
*The quantum smooth label cover problem is undecidable*, arXiv:2510.03477v3,
defines acceptance on `e=(v,w)` by the single equality

```text
pi_(e,v)(a)=pi_(e,w)(b).
```

The fibers of a function partition its domain, so sorting the accepted pairs
by the common value proves `(SLC1)`.  For `(SLC2)--(SLC3)`, multiplication by
`mu_r` preserves magnitude.  Distinct positive magnitudes therefore lie in
distinct projective phase orbits, and the monomial winning equation is
solvable exactly when the two projection values agree.  This is the same
projective-color criterion classified by
`monomial-game-pair-compatibility-is-projective-color-rigid`.
