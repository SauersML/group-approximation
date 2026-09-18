---
rg: 2
id: cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class
kind: claim
title: Every virtually torsion-free group acting geometrically on an irreducible symmetric space of noncompact type times a locally finite tree lies in the permutational Boone--Higman class
distinct_from:
  cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class: that settles X = H^2 with no torsion hypothesis, and other X only for residually finite arithmetic fibres; this settles every irreducible X for virtually torsion-free groups, arithmetic or not.
  commensurator-rigid-bs-classes-are-virtual-products: that is the structure theorem for fibre groups of finite index in their commensurator; this combines it with the faithful-member route into a dichotomy that leaves no case open.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for every CAT(0) group; this is the subclass on X x T.
---

**ESTABLISHED** through `cat0-symmetric-space-tree-type-a-proof` (lane proof;
not independently reviewed; no priority claimed).

**Statement.** Let `X` be an irreducible Riemannian symmetric space of noncompact
type, and `T` a locally finite tree. Let `Γ` act properly and cocompactly by
isometries on `X × T`, preserving the product decomposition. The decomposition is
preserved automatically when `T` has a branch point or is a line. If `Γ` is
virtually torsion-free, then `Γ ∈ B_A`, so `Γ` and all its subgroups embed in
finitely presented simple groups.

**The dichotomy behind it.** Let `G` be a torsion-free fibre group of a finite-index
subgroup `Γ_1`: a cocompact lattice in `Isom(X)`.
- **Commensurator non-discrete** (the arithmetic case, and every `G` when `X = H^2`,
  via surface groups): faithful Hecke members exist, and `BS_G ⊆ B_A`
  (`arithmetic-lie-lattices-have-faithful-bs-members`).
- **Commensurator discrete** (non-arithmetic, which is possible only for `H^n`,
  `n >= 3`, and `CH^n`, `n >= 2`): `Γ_1` is virtually `N × F` with `N` a lattice and
  `F` virtually free (`commensurator-rigid-bs-classes-are-virtual-products`). So it is
  linear in characteristic zero.

**Remarks.**
- `Γ` need not be linear or residually finite. In the first case only its fibres
  are constrained.
- For `X = H^2` the torsion hypothesis is unnecessary:
  `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`.
- Not covered:
  - groups on `X × T` that are not virtually torsion-free;
  - reducible `X` with a non-arithmetic factor lattice;
  - `X` with a Euclidean factor, which is outside this node except for
    `cat0-groups-with-a-tree-factor-lie-in-type-a-class`, instance (a).
