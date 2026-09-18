---
rg: 2
id: cat0-groups-with-a-tree-factor-lie-in-type-a-class
kind: claim
title: A CAT(0) group on a product with a tree factor lies in the permutational Boone--Higman class whenever its fibre group has a faithful Baumslag--Solitar member; in particular every CAT(0) group on Euclidean space times a tree does
distinct_from:
  cat0-groups-satisfy-boone-higman: that is survey item (10) for every CAT(0) group; this settles the subclass acting on a product Y x T with a tree factor T, under a condition on the fibre group only.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that is the case Y = tree; this allows any proper CAT(0) fibre Y, and recovers that node as an instance.
  product-of-trees-lattices-satisfy-permutational-boone-higman: that asks for every lattice in any product of trees and is blocked by non-residually-finite factor stabilizers; this covers the products whose tree-vertex stabilizers are commensurable with a group G that has a faithful BS_G member, such as an arithmetic quaternion lattice.
  bs-class-with-faithful-member-lies-in-type-a-class: that is the general BS_G statement; this shows that CAT(0) groups with a tree factor lie in BS_G for their fibre group G.
---

**ESTABLISHED** through `cat0-tree-factor-type-a-proof` (lane proof; not
independently reviewed; no priority claimed).

**Setting.** `Y` is a proper CAT(0) space and `T` a locally finite tree. `Γ` acts
properly and cocompactly by isometries on `Y × T`, preserving the product
decomposition. `G` is the `Γ`-stabilizer of a vertex of `T`.

1. `G` acts properly and cocompactly on `Y`, so it is finitely presented. Every
   vertex and edge stabilizer of the action on `T` is abstractly commensurable
   with `G`, and `Γ ∈ BS_G`.
2. If `BS_G` has a nontrivial member acting faithfully on its Bass--Serre tree,
   then `Γ ∈ B_A`. So `Γ` and all its subgroups embed in finitely presented simple
   groups.

**Instances.**
- **(a) Euclidean times tree.** Let `Γ` act properly and cocompactly by isometries
  on `E^n × T`, `n >= 0`. Then `Γ ∈ B_A`.
  - Product preservation is automatic when `T` has a vertex of degree `>= 3`. When
    it has none, `Γ` is virtually free abelian.
  - This includes every Leary--Minasyan group. BLIW Corollary 12.4 states plain
    Boone--Higman for these; this is the permutational form for every lattice on
    `E^n × T`, not only commensurating HNN extensions of `Z^n`.
- **(b) Tree times tree.** `Y` a locally finite tree gives
  `product-of-two-trees-lattices-satisfy-permutational-boone-higman` again.
- **(c) Arithmetic quaternion fibres.** Let `Y = T_(p+1) × T_(q+1)`, and let `G`
  be abstractly commensurable with a definite quaternion lattice `Λ` as in
  instance 2 of `arithmetic-nsp-lattices-have-faithful-bs-members`. Then `Γ ∈ B_A`.
  This gives lattices in products of three trees whose stabilizers of vertices of
  one factor are commensurable with such `Λ`, with no faithfulness or
  separating-factor hypothesis.

**Not covered.**
- Fibre groups `G` for which no faithful member of `BS_G` is known. That includes
  every non-residually-finite `G`, such as Wise or Burger--Mozes fibres in products
  of three trees.
- Products with no tree factor, such as exotic Ã₂ buildings (`exotic-a2-lattices-satisfy-boone-higman`).
