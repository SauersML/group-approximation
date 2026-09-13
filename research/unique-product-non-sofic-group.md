---
rg: 2
id: unique-product-non-sofic-group
kind: claim
title: Exhibit a nonsofic group with unique products
distinct_from:
  left-orderable-non-sofic-group: that asks for a left-orderable witness, which conjecturally excludes property (T); this asks only for unique products, which infinite Kazhdan groups can have, so the rigid-defect mechanism is not excluded.
---

**Statement (OPEN).**  Some group with the unique product property is not
sofic.

**Why it matters.**  A group `W` with unique products satisfies, over every
field `K`, Kaplansky's unit and zero-divisor conjectures.  So `K[W]` is a
domain, hence directly finite.  The torsion-free counterexample hosts hunted in
this graph are nonsofic.  A nonsofic group with unique products would show that
nonsoficity alone does not produce zero divisors or nontrivial units.  No
nonsofic group satisfying either conjecture is recorded in this graph.  Direct
finiteness alone is known for the torsion-containing Kun--Thom wreaths
(`kun-thom-wreath-stably-finite`).

**Property (T) is no obstacle here.**  Kionke--Raimbault, arXiv:1411.6449v2,
p. 3, Theorem B: "If Γ is a lattice in one of the Lie groups SO(n,1), SU(n,1)
or Sp(n,1) then there is a finite-index subgroup Γ' ≤ Γ such that Γ' is
diffuse."  Diffuse groups have unique products (same paper, p. 1, after
Bowditch).  Lattices in `Sp(n,1)` are Kazhdan.  So infinite Kazhdan groups with
unique products exist, unlike the left-orderable case
(`infinite-left-orderable-kazhdan-group`).

## Attempts

**Through left-orderability.**  `unique-product-non-sofic-from-left-orderable`.
This is gated by Navas's Question 3 for every known mechanism.

**Residual finiteness of a hyperbolic rigid-pair host.**
`rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` says a residually
finite hyperbolic group containing an infranormal non-normal Kazhdan pair
yields a unique-product nonsofic group.  One such host, the hyperbolic Kazhdan
cover of the Leavitt unit group, exists.  So
`non-rf-hyperbolic-group-or-unique-product-nonsofic-group` holds: either
Gromov's question has a negative answer, or this claim is true.  The open input
is residual finiteness of that one cover.

**Known nonsofic groups directly.**

- The Leavitt unit group, the Kun--Thom wreath and its Theorem E double contain
  torsion, so none of them has unique products.
- For the Fournier--Facio group, unique products are unknown.  Its source group
  contains a universal torsion-free group, and so non-unique-product groups
  such as Promislow's.  But the quotient map is known to be injective only on a
  finite ball and on `S` (`fournier-facio-group-hyperlinear`, "No universality").
  So no obstruction transfers.

**A unique-product Kazhdan lattice as the rigid subgroup.**  Blocked as stated.
A strict compression `t Gamma t^-1 < Gamma` is an injective, non-surjective
endomorphism of `Gamma`.  Kazhdan groups have property FA, so a torsion-free
hyperbolic Kazhdan group is freely indecomposable.  Such groups are co-Hopfian
(Sela, GAFA 1997; not re-read here).  So the compression has to act on a
non-hyperbolic subgroup of a larger host, as in the Leavitt cover, where the
compressed subgroup is not quasiconvex.

**Characteristic-zero Kun--Thom actors.**
`char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup` supplies
torsion-free finite-index subgroups.  Whether Kun--Thom Theorem E holds in
characteristic zero is not checked in the graph.  These groups contain
torsion-free finite-index subgroups of `SL_3(Z)`.  Unique products for those
are not recorded here, and the literature was not checked on this point.
