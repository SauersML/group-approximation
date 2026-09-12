---
rg: 2
id: o2-z2-actions-fix-a-cartan-subalgebra
kind: claim
title: Every outer strongly approximately inner Z_2-action on O_2 leaves some Cartan subalgebra invariant
distinct_from:
  uct-for-two-infinity-absorbing-nuclear-algebras: that is a UCT statement about all M_{2^∞}-stable nuclear algebras; this is the equivalent dynamical statement about order-two automorphisms of O_2 alone.
  cartan-respecting-o2-automorphisms-give-uct-crossed-products: that proves the UCT for the automorphisms that already preserve a Cartan subalgebra; this asks that every outer strongly approximately inner order-two action does.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Every outer strongly approximately inner action `β : Z_2 ↷ O_2`
leaves some Cartan subalgebra `B ⊆ O_2` globally invariant (equivalently, by
Barlak--Li Theorem 1.8, fixes some Cartan subalgebra pointwise).  By
`barlak-li-two-half-iff-z2-actions-fix-cartan` this is equivalent to
`uct-for-two-infinity-absorbing-nuclear-algebras`, the half of Problem II
localized at 2.

## Attempts

* **Automorphisms that already carry a Cartan.**  Gauge-type automorphisms
  `λ_u(s_i) = u s_i` with `u` in the unitary normalizer of `D_2`, which includes
  the Thompson group `V` of the Leavitt region, preserve `D_2`.  Tensor flips of
  `O_2 ⊗ O_2 ≅ O_2` preserve the product Cartan subalgebra.  So every order-two
  element of these families is covered
  (`cartan-respecting-o2-automorphisms-give-uct-crossed-products`).  This proves
  nothing about an arbitrary action in Izumi's class, which is characterized
  by an invariant of approximate representability, not by a masa.  Dies at the
  general action.
* **Constructing the Cartan from strong approximate innerness.**  Strong
  approximate innerness (Izumi's definition) supplies unitaries implementing
  `β` approximately.  An invariant Cartan subalgebra would need those unitaries
  to normalize a common masa coherently along the approximation.  Izumi's
  classification matches these actions with their crossed products, which by
  Barlak--Li statement 2 range over all unital `M_(2^∞)`-absorbing Kirchberg
  algebras in Cuntz standard form, UCT or not.  So the classification alone
  supplies no coherence.  Not carried further.
