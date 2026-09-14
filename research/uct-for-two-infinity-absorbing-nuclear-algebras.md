---
rg: 2
id: uct-for-two-infinity-absorbing-nuclear-algebras
kind: claim
title: Every separable nuclear M_(2^∞)-absorbing C*-algebra satisfies the UCT
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the UCT for all separable nuclear algebras; this is its half localized at the prime 2, equivalent to Problem II only together with the half localized at an odd prime.
  uct-for-three-infinity-absorbing-nuclear-algebras: that is the half localized at 3; the two halves share only the coprime splitting.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Every separable nuclear `A` with `A ≅ A ⊗ M_{2^∞}` satisfies the UCT.
Equivalently, `A ⊗ M_{2^∞}` satisfies the UCT for every separable nuclear `A`.
By `coprime-uhf-stabilizations-detect-uct` this half, together with
`uct-for-three-infinity-absorbing-nuclear-algebras`, gives Problem II.

## Attempts

* **Order-two automorphisms of `O_2`.**  Barlak--Li Theorem 1.8 makes this half
  exactly equivalent to `o2-z2-actions-fix-a-cartan-subalgebra`: every outer
  strongly approximately inner `Z_2`-action on `O_2` leaves a Cartan subalgebra
  invariant (`barlak-li-two-half-iff-z2-actions-fix-cartan`, route
  `uct-two-half-via-z2-actions-on-o2`).  Every order-two automorphism that
  already leaves a Cartan subalgebra invariant is harmless
  (`cartan-respecting-o2-automorphisms-give-uct-crossed-products`).  Dies at
  actions with no invariant Cartan subalgebra.
* **Localized Kirchberg reduction.**  The half reduces again to trivial-K-theory
  Kirchberg algebras absorbing `M_{2^∞}`.  Such algebras carry Rokhlin actions of
  `Z/2` coming from the UHF factor, but no argument turning a Rokhlin action
  into a KK-contraction is known.  Dies there.
