---
rg: 2
id: whitehead-recursively-presented-via-injective-embedding
kind: route
title: A Whitehead-injective embedding pushes the finitely presented case down
target: whitehead-vanishing-recursively-presented-torsion-free
requires: [whitehead-vanishing-finitely-presented-torsion-free, whitehead-injective-torsion-free-embedding]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Let `K` be finitely generated, recursively presented and torsion-free.  The
second hypothesis provides an embedding `K -> H` with `H` finitely presented
and torsion-free such that `Wh(K) -> Wh(H)` is injective.  The first gives
`Wh(H) = 0`.  An injection into the zero group has zero source, so
`Wh(K) = 0`.

## The whole content is in the injectivity hypothesis

The embedding itself is not the issue and has not been for some time:
`torsion-free-higman-embedding` supplies it outright, uniformly and with an
explicit map.  What no construction supplies is control of the kernel of the
induced map on Whitehead groups, and the two natural repairs both fail --
a retraction is too strong to exist in general (a retract of a finitely
presented group is finitely presented), and finite-pattern transplantation
moves the matrix without moving the factorization back.  Composed with
`whitehead-global-via-recursively-presented-reduction`, this route is exactly
one theorem away from the conjecture, and that theorem is entirely about
`K_1`, not about groups.
