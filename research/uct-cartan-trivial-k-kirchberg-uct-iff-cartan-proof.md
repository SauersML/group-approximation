---
rg: 2
id: uct-cartan-trivial-k-kirchberg-uct-iff-cartan-proof
kind: route
title: Pass from the UCT to O_2 by unital KK-classification, from O_2 to its canonical diagonal, and back by Barlak--Li
target: uct-cartan-trivial-k-kirchberg-uct-iff-cartan
requires: [kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras, barlak-li-cartan-subalgebras-force-uct]
artifacts:
  - research/artifacts/uct-cartan-obstruction-2026-09-12.md
---

Let `A` be a unital Kirchberg algebra with `K_*(A) = 0`.

**1 ⟹ 2.**  If `A` satisfies the UCT, the UCT sequence for `KK(A, A)` has zero
`Hom` and `Ext` terms, so `KK(A, A) = 0` and `[id_A] = 0`.  So `A` is
KK-equivalent to `O_2` by an element preserving the (zero) unit classes, and
Kirchberg--Phillips classification gives `A ≅ O_2`.  This is the mechanism
recorded in `kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`.

**2 ⟹ 3.**  The canonical diagonal `D_2 ⊆ O_2` is a Cartan subalgebra; `(O_2, D_2)`
is the Cartan pair of Barlak--Li Theorem 1.4
(`barlak-li-cartan-subalgebras-force-uct`).  An isomorphism carries it to a Cartan
subalgebra of `A`.

**3 ⟹ 1.**  `A` is separable and nuclear, so a Cartan subalgebra gives the UCT by
Barlak--Li Corollary 1.2 (`barlak-li-cartan-subalgebras-force-uct`).

**Consequence.**  If a unital trivial-K Kirchberg algebra has no Cartan
subalgebra, it fails the UCT by 1 ⟹ 3.  Conversely, if some separable nuclear
algebra fails the UCT, then by
`kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras` some unital trivial-K
Kirchberg algebra `A` is not isomorphic to `O_2`, and by 2 ⟺ 3 it has no Cartan
subalgebra.
