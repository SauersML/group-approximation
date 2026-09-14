---
rg: 2
id: uct-for-three-infinity-absorbing-nuclear-algebras
kind: claim
title: Every separable nuclear M_(3^∞)-absorbing C*-algebra satisfies the UCT
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the UCT for all separable nuclear algebras; this is its half localized at the prime 3, equivalent to Problem II only together with a coprime half such as the one at 2.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**OPEN.**  Every separable nuclear `A` with `A ≅ A ⊗ M_{3^∞}` satisfies the UCT.
Equivalently, `A ⊗ M_{3^∞}` satisfies the UCT for every separable nuclear `A`.
Together with `uct-for-two-infinity-absorbing-nuclear-algebras` it gives
Problem II through `coprime-uhf-stabilizations-detect-uct`; any other prime would
serve in place of `3`.

## Attempts

* **Order-three automorphisms of `O_2`.**  Barlak--Li's crossed-product
  criterion covers `O_2 ⋊_α Z_p` for every prime `p`: the UCT follows when some
  `γ(D_2)` is regular in the crossed product.  Cartan-respecting automorphisms
  of order three are harmless
  (`cartan-respecting-o2-automorphisms-give-uct-crossed-products`).  The abstract
  read states the `M_{2^∞}` relation only, and no odd-prime analogue has been
  checked from the source.  Dies at the same wall as the half at `2`: exotic
  automorphisms with no invariant Cartan subalgebra.
