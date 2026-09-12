---
rg: 2
id: gardella-rokhlin-actions-preserve-uct
kind: claim
title: Fixed point algebras and crossed products of Rokhlin compact group actions on simple nuclear UCT algebras satisfy the UCT
distinct_from:
  uct-class-permanence-properties: that lists the general permanence properties of the UCT class; this is permanence along crossed products and fixed point algebras by compact group actions with the Rokhlin property.
  izumi-rokhlin-approximately-representable-duality: that is the duality between the Rokhlin property and approximate representability; this is the downward permanence of the UCT along Rokhlin actions.
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

**ESTABLISHED (literature).**  Gardella, *Crossed products by compact group
actions with the Rokhlin property*, arXiv:1408.1946, Theorem 3.13. Let `A` be a
separable, simple, nuclear C\*-algebra, `G` a second-countable compact group,
and `α : G → Aut(A)` an action with the Rokhlin property. If `A` satisfies the
UCT, then so do `A^α` and `A ⋊_α G`.

Proof: `gardella-rokhlin-actions-preserve-uct-citation`.

**Definition used.**  Gardella's Definition 2.2 asks, for every separable
invariant subalgebra `D`, for an equivariant unital homomorphism
`(C(G), Lt) → F(D, A)`. The introduction says the Hirshberg--Winter definition
it extends coincides with Izumi's for finite groups. For unital separable `A`
and finite `G`, this is the Rokhlin property used in Barlak--Li II
(Definition 2.6), recorded in `izumi-rokhlin-approximately-representable-duality`.

**Bearing on Problem II.**  For a Rokhlin action `δ : Z_p ↷ B` on a unital
Kirchberg algebra, the UCT passes *down* from `B` to `B ⋊_δ Z_p` and `B^δ`. By
`o2-zp-cartan-fixing-iff-rokhlin-uct-ascent`, the prime half of Problem II is
exactly the converse: the UCT passing *up* from `B ⋊_δ Z_p ≅ O_2` to `B`.
