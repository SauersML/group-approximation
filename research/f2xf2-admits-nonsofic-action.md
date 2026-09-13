---
rg: 2
id: f2xf2-admits-nonsofic-action
kind: claim
title: F2 x F2 has an essentially free p.m.p. action that is not sofic
distinct_from:
  f2xf2-in-paunescu-class: that is the negation
  kun-thom-free-nonsofic-action: that is a nonsofic action of a Kazhdan group through a Kazhdan subgroup; this asks for one of a Haagerup group, which has no infinite Kazhdan subgroup
  mixing-free-nonsofic-action-of-sofic-group: that asks for a mixing nonsofic action of some sofic group; this fixes the group F2 x F2 and asks for any free nonsofic action
---

**OPEN.** `F_2 × F_2` admits an essentially free p.m.p. action that is not sofic
(Păunescu Definition 1.4). Since `F_2 × F_2` is residually finite, this would be a
nonsofic action of a sofic group with the Haagerup property.

## Attempts

* **Kun--Thom Theorem C.** Needs an infinite Kazhdan subgroup. `F_2 × F_2` has
  the Haagerup property, which passes to subgroups and excludes infinite Kazhdan
  groups. Co-induction from a subgroup needs a subgroup outside `𝒮`, and every
  subgroup is again Haagerup. Dies.
* **From a nonsofic lattice in a product of trees.** Live and conditional:
  `f2xf2-nonsofic-action-from-radu-lattice-nonsofic`. Any nonsofic cocompact
  lattice in `Aut(T_p) × Aut(T_q)` works, by
  `product-tree-lattices-in-paunescu-class-iff-f2xf2`.
* **From any group measure equivalent to `F_2 × F_2` outside `𝒮`.** By
  `paunescu-class-is-measure-equivalence-invariant` one such group suffices, sofic
  or not, with the explicit transfer recorded there.
