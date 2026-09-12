---
rg: 2
id: o2-z3-actions-fix-a-cartan-subalgebra
kind: claim
title: Every outer strongly approximately inner Z_3-action on O_2 leaves some Cartan subalgebra invariant
distinct_from:
  o2-z2-actions-fix-a-cartan-subalgebra: that is the same statement for Z_2-actions; together the two are equivalent to Problem II by Barlak--Li II Theorem 1.4.
  uct-for-three-infinity-absorbing-nuclear-algebras: that is the UCT for M_(3^∞)-absorbing nuclear algebras; Barlak--Li II Theorem 4.16 proves it equivalent to this dynamical statement about order-three automorphisms of O_2.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

**OPEN.**  Every outer strongly approximately inner action `α : Z_3 ↷ O_2`
leaves some Cartan subalgebra `B ⊆ O_2` globally invariant.  Together with
`o2-z2-actions-fix-a-cartan-subalgebra` this is equivalent to Problem II
(`barlak-li-uct-iff-z2-z3-actions-fix-cartan`).  On its own it is equivalent to
`uct-for-three-infinity-absorbing-nuclear-algebras`
(`barlak-li-p-half-iff-zp-actions-fix-cartan`).

## Attempts

* **Automorphisms that already carry a Cartan.**  Order-three gauge
  automorphisms `λ_u` with `u` in the normalizer of `D_2`, for instance
  order-three elements of Thompson's group `V`, preserve `D_2`.  So does the
  cyclic shift of `O_2 ⊗ O_2 ⊗ O_2 ≅ O_2`, which preserves `D_2 ⊗ D_2 ⊗ D_2` by
  the argument of `cartan-respecting-o2-automorphisms-proof`.  Whether these
  actions are outer and strongly approximately inner was not checked, and in
  any case they say nothing about a general action in Izumi's class.  Dies at
  the general action.
* **Via Barlak--Li II Theorem 1.2.**  For such `α` the crossed product
  `O_2 ⋊_α Z_3` absorbs `M_(3^∞)` (their Corollary 4.15), and an invariant
  Cartan subalgebra exists iff the crossed product satisfies the UCT.  This
  restates the claim as a UCT statement for one family of `M_(3^∞)`-absorbing
  Kirchberg algebras and does not prove it.  Theorem 4.16 of the same paper
  upgrades the family statement to an exact equivalence with the UCT half at 3,
  now the route `uct-three-half-via-z3-actions-on-o2`.
* **Actions named by equivariant classification.**  Every such action that is
  `KK^(Z_3)`-equivalent to an action on a type I algebra fixes a Cartan subalgebra
  (`bootstrap-class-zp-actions-on-o2-fix-a-cartan`).  So the classification
  theory of pointwise outer cyclic actions (Köhler; Meyer--Nadareishvili,
  arXiv:2604.12529v2; Gabe--Szabó) cannot supply a counterexample.  Dies at the
  boundary of the equivariant bootstrap class.
