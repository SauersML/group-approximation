---
rg: 2
id: stw99-problem-lxiv-cu-of-villadsen-toms
kind: claim
title: Compute the Cuntz semigroup of the stable-rank-one Villadsen-Toms counterexamples (STW Problem LXIV, Gardella-Perera)
root: true
artifacts:
  - research/artifacts/stw99-structural-cu-cluster-2026-08-30.md
  - research/artifacts/stw64-supersoft-comparison-gap-2026-09-04.md
---

**Problem LXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Gardella--Perera Questions 16.1--16.3).  What is `Cu` of the
Villadsen/Toms classification counterexamples with stable rank one —
and are there two DISTINCT `Cu`-morphisms `Cu(Z) → Cu(A)` there?

## Attempts and correction (2026-09-04)

The problem remains open. Gardella--Perera Problem 16.3 explicitly asks
that both morphisms preserve the unit class.

Thiel's rank-realization theorem gives the existence of elements with
prescribed ranks. It does not compute their complete equivalence and order
structure. The previous claim that stable rank one makes the soft part
known, or realizes every rank-respecting comparison, was unsupported.
Projection Chern obstructions do not supply the missing soft classification.

There is now an exact obstruction to one proposed construction.
`stw64-supersoft-gap-is-comparison-radius` identifies the infimum of
`b-a` with `alpha(a*u-hat)<<alpha(b*u-hat)` as `rc(A)`.
`stw64-z-maps-avoid-supersoft-classes` consequently proves that if
`rc(A)>0`, every unit-preserving `f:Cu(Z)->Cu(A)` lies strictly below the
canonical supersoft class `alpha(t*u-hat)` at every finite positive soft
real `t`. Equality at even one such value would force `rc(A)=0`.

Thus an existing map and the canonical supersoft family do not give the
desired pair: the latter fails to be a Cu-morphism. Two different coherent
soft scales still have to be constructed and checked, including their
compact-containment and unit relations.

The connection to LXIII remains: the route
`stw99-lxiv-pair-lifts-to-lxiii-refuter` uses Robert's existence theorem to
lift an actual unit-compatible pair to inequivalent unital embeddings.
No such pair is supplied by the new obstruction.
