---
rg: 2
id: contractible-2-complex-minus-a-cell-is-aspherical
kind: claim
title: Removing one open 2-cell from a finite contractible 2-complex always leaves an aspherical complex
distinct_from:
  whitehead-asphericity-conjecture: that covers every subcomplex of every aspherical 2-complex, infinite ones included; this is only the finite case where one 2-cell of a contractible complex is removed.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that is the existence of some non-aspherical subcomplex of a contractible 2-complex; a counterexample to this claim would establish it, but its witness need not be a one-cell complement.
  whitehead-one-cell-counterexamples-have-positive-first-l2-betti: that is an established constraint on non-aspherical one-cell complements; this is the open statement that there are none.
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

**OPEN.** For every finite connected contractible 2-complex L and every open 2-cell e of L,
the subcomplex L − e is aspherical.

- It is the special case of `whitehead-asphericity-conjecture` with Y = L and K = L − e.
  Howie's reduction (1983, recalled, not pinned) splits a Whitehead counterexample into
  this finite type and an infinite ascending-union type.
- LOT complexes are instances (item 1 of
  `lot-complexes-with-vanishing-first-l2-betti-are-aspherical`), so the claim contains the
  open question of whether every LOT complex is aspherical.
- Into it: the route `one-cell-l2-vanishing-gives-one-cell-whitehead`.
- Out of it: the route `kervaire-killing-form-via-one-cell-whitehead`. So this finite case
  alone already implies the killing form of Kervaire--Laudenbach over nonnegative
  deficiency.
