---
rg: 2
id: o2-z3-actions-fix-a-cartan-subalgebra
kind: claim
title: Every outer strongly approximately inner Z_3-action on O_2 leaves some Cartan subalgebra invariant
distinct_from:
  o2-z2-actions-fix-a-cartan-subalgebra: that is the same statement for Z_2-actions; together the two are equivalent to Problem II by Barlak--Li II Theorem 1.4.
  uct-for-three-infinity-absorbing-nuclear-algebras: that is the UCT for M_(3^∞)-absorbing nuclear algebras; no source read proves it equivalent to this dynamical statement, which enters only through the joint equivalence with the Z_2 case.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Every outer strongly approximately inner action `α : Z_3 ↷ O_2`
leaves some Cartan subalgebra `B ⊆ O_2` globally invariant.  Together with
`o2-z2-actions-fix-a-cartan-subalgebra` this is equivalent to Problem II
(`barlak-li-uct-iff-z2-z3-actions-fix-cartan`).

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
  Kirchberg algebras and does not prove it.  Recorded as a restatement, not a
  route.
