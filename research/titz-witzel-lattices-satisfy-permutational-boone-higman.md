---
rg: 2
id: titz-witzel-lattices-satisfy-permutational-boone-higman
kind: claim
title: The non-residually-finite Titz Mite--Witzel C2-tilde lattices satisfy permutational Boone--Higman
distinct_from:
  titz-witzel-simple-kazhdan-cat0-lattices-exist: that imports the lattices, their simple finite-index kernels and property (T); this asks whether the lattices lie in the class B_A.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that settles the product-of-trees lattices, such as Radu's lattice, which sits inside one of these kernels up to index four; this asks for the irreducible C2-tilde lattices themselves.
artifacts:
  - research/artifacts/solve-bh-cat0-automatic-2026-09-13.md
---

**OPEN.** Each lattice `Γ_i^q = π_1(Y_i^q)` of Titz Mite--Witzel lies in `B_A`.
That is, it embeds in a finitely presented group with an action of type (A).

- **The kernels.** Their simple finite-index kernels `Γ̌_i^q` are finitely
  presented and simple, so the Boone--Higman conclusion holds for them
  trivially.
- **The lattices.** Each `Γ_i^q` has a nontrivial finite quotient. Main has no
  closure of the Boone--Higman class under finite-index overgroups. The class
  `B_A` does have it, by `boone-higman-type-a-class-closed-under-finite-extensions`.

**Why these lattices.** They are CAT(0) groups with property (T), and they are
not residually finite. So every tree, linear, hyperbolic and self-similar method
fails for them, as recorded on `cat0-groups-satisfy-boone-higman`.

**Route.** `titz-witzel-lattices-pbh-from-mif-kernels` reduces this claim to
`titz-witzel-kernels-are-mif`.
