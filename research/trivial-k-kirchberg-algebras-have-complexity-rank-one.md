---
rg: 2
id: trivial-k-kirchberg-algebras-have-complexity-rank-one
kind: claim
title: Every unital Kirchberg algebra with zero K-theory decomposes over finite-dimensional algebras
distinct_from:
  trivial-k-theory-kirchberg-algebras-are-o2: that asks for an isomorphism with O_2; this asks for a local two-piece finite-dimensional decomposition with an approximate intersection, which Willett--Yu show is equivalent but which is a different object to construct.
  kirchberg-algebras-have-weak-complexity-rank-one: that is the established two-colour statement with no intersection algebra; this demands the intersection algebra as well.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Every unital Kirchberg algebra `A` with `K_*(A) = 0` has complexity
rank at most one: it decomposes, in the sense of Willett--Yu Definition 1.1,
over the class of finite-dimensional C\*-algebras.  By
`willett-yu-decomposability-forces-uct` this is equivalent to Problem II.

## Attempts

* **Upgrade from weak complexity rank one.**  Every Kirchberg algebra has weak
  complexity rank at most one (`kirchberg-algebras-have-weak-complexity-rank-one`):
  finite-dimensional `C, D ∋ 1` and an approximately central `h` cutting `A`
  into them.  What is missing is a finite-dimensional `E ∋ h` that contains
  `h(1 − h)x` approximately and is ε-contained in both `C` and `D`.  The general
  upgrade is false (`weak-complexity-rank-one-does-not-imply-rank-one`: torsion in
  `K_1`).  For `K_*(A) = 0` that obstruction is absent, but no construction of
  `E` is known.  Dies at producing `E`.
* **Near inclusions.**  Christensen's perturbation theorem for near inclusions
  (Acta Math. 144 (1980)) turns an ε-inclusion of a finite-dimensional algebra
  into a genuine inclusion after conjugating by a unitary close to `1`, so `E`
  could be moved inside `C` or inside `D`.  The difficulty is doing both at
  once.  A nuclear-dimension-one decomposition supplies two order-zero colours
  with no common finite-dimensional overlap, and the unitary that moves `E`
  into `D` does not keep it inside `C`.  Dies at simultaneous containment.
