---
rg: 2
id: cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class
kind: claim
title: Every group with virtually torsion-free fibre groups acting geometrically on an irreducible symmetric space of noncompact type times a locally finite tree lies in the permutational Boone--Higman class
distinct_from:
  cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class: that settles X = H^2 with no torsion hypothesis, and other X only for residually finite arithmetic fibres; this settles every irreducible X for virtually torsion-free groups, arithmetic or not.
  commensurator-rigid-bs-classes-are-virtual-products: that is the structure theorem for fibre groups of finite index in their commensurator; this combines it with the faithful-member route into a dichotomy that leaves no case open, with a hypothesis on the fibre groups only.
  cat0-groups-satisfy-boone-higman: that is survey item (10) for every CAT(0) group; this is the subclass on X x T.
---

**ESTABLISHED** through `cat0-symmetric-space-tree-type-a-proof` (lane proof;
not independently reviewed; no priority claimed).

**Statement.** Let `X` be an irreducible Riemannian symmetric space of noncompact
type, and `T` a locally finite tree. Let `Γ` act properly and cocompactly by
isometries on `X × T`, preserving the product decomposition. The decomposition is
preserved automatically when `T` has a branch point or is a line. If the
stabilizers `Γ_v` of vertices of `T` are virtually torsion-free, which holds, for example, when `Γ` is virtually torsion-free or `Γ_v` is residually
finite, then `Γ ∈ B_A`. So `Γ` and all its subgroups embed in
finitely presented simple groups.

**The dichotomy behind it.** Let `G_0` be a torsion-free finite-index subgroup of a fibre group `Γ_v`. It is
a cocompact lattice in `Isom(X)`, and `Γ ∈ BS_(G_0)`.
- **Commensurator non-discrete** (the arithmetic case, and every `G_0` when `X = H^2`,
  via surface groups): faithful Hecke members exist, and `BS_(G_0) ⊆ B_A`
  (`arithmetic-lie-lattices-have-faithful-bs-members`).
- **Commensurator discrete** (non-arithmetic, which is possible only for `H^n`,
  `n >= 3`, and `CH^n`, `n >= 2`): `Γ` is virtually `K × F` with `K` commensurable
  with `G_0` and `F` free (`commensurator-rigid-bs-classes-are-virtual-products`). A finite-index
  subgroup `K_0 × F` of it is linear in characteristic zero, so `Γ ∈ B_A`.

**Remarks.**
- `Γ` need not be linear or residually finite. In the first case only its fibres
  are constrained.
- For `X = H^2` the torsion hypothesis is unnecessary:
  `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`.
- Not covered:
  - groups on `X × T` whose fibre groups are not virtually torsion-free, which is
    possible only through non-residually-finite finite central extensions of lattices;
  - reducible `X` with a non-arithmetic factor lattice;
  - `X` with a Euclidean factor, which is outside this node except for
    `cat0-groups-with-a-tree-factor-lie-in-type-a-class`, instance (a).
