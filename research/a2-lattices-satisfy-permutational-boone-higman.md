---
rg: 2
id: a2-lattices-satisfy-permutational-boone-higman
kind: claim
title: Every cocompact lattice of a locally finite thick Ã2 building, exotic or not and torsion allowed, lies in the type (A) class
distinct_from:
  a2-lattices-embed-in-fp-simple-groups: that embeds each such lattice in an infinite simple group of type F_infinity; this puts it in the permutational class B_A, which is closed under finite-index overgroups, direct products and subgroups.
  exotic-a2-lattices-satisfy-boone-higman: that is the plain Boone--Higman form for exotic buildings (now ESTABLISHED through `a2-lattices-embed-in-fp-simple-groups`); this gives the permutational form for cocompact lattices, through the host of bh-groupoid.
---

**ESTABLISHED** through `a2-lattices-pbh-via-stabilized-orbit-category` (lane proof;
not independently reviewed; no priority claimed). The host is bh-groupoid's, and
this node only adds the type (A) step.

**Statement.** Let `B` be a locally finite thick Ã₂ building and `Γ ≤ Aut(B)`
discrete and cocompact. Then `Γ` embeds in a finitely presented group with an action
of type (A). So `Γ ∈ B_A`, and every subgroup of `Γ` embeds in a finitely presented
simple group.

**Consequences beyond the simple-host statement.** `B_A` is closed under
finite-index overgroups, finite direct products and subgroups
(`boone-higman-type-a-class-closed-under-finite-extensions`). So:
- products of finitely many Ã₂ lattices are in `B_A`;
- products of Ã₂ lattices with lattices on products of trees
  (`cocompact-tree-product-lattices-lie-in-type-a-class`) are in `B_A`;
- every group containing such a product with finite index is in `B_A`.

**Lesson for general BH.** Once a simple host is a full group of a finitely coded
groupoid, upgrading to the permutational class costs nothing beyond strong
connectivity of the coding: the stabilized comparison lemma turns the same host
into a type (A) actor. So PBH, and with it closure under finite-index overgroups
and products, comes free with every coded host.
