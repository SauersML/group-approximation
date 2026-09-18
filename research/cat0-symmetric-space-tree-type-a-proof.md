---
rg: 2
id: cat0-symmetric-space-tree-type-a-proof
kind: route
title: Split along the tree; a torsion-free fibre lattice either has a non-discrete commensurator, giving a faithful Hecke member, or forces a virtual product, which is linear
target: cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class
requires: [cat0-groups-with-a-tree-factor-lie-in-type-a-class, arithmetic-lie-lattices-have-faithful-bs-members, commensurator-rigid-bs-classes-are-virtual-products, cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Product preservation.** If `T` has a branch point, `X × T` has no Euclidean
factor, and `X` and `T` are non-isometric irreducible factors. If `T` is a line,
`R` is the Euclidean de Rham factor. Either way isometries preserve the
decomposition (Foertsch--Lytchak; cited, not re-read). Otherwise it is a hypothesis.

**Step 1 (torsion-free reduction).** Let `Γ_1 ≤ Γ` be torsion-free of finite index.
By item 1 of `cat0-groups-with-a-tree-factor-lie-in-type-a-class`, `Γ_1 ∈ BS_G`,
where `G = (Γ_1)_v` acts properly and cocompactly on `X × {v}`.
- `G` is torsion-free, so it acts freely, hence faithfully, on `X`.
- So `G` is a torsion-free cocompact lattice in `Isom(X)`.
- `G_0 = G ∩ Isom(X)^0` has finite index in `G`.
- All vertex groups of the splitting of `Γ_1` are torsion-free.

Put `L = Isom(X)^0`. It is simple with trivial center, and irreducibility of `G_0` is
automatic.

**Step 2a (commensurator non-discrete).** If `Comm_L(G_0)` is not discrete, the
theorem of `arithmetic-lie-lattices-have-faithful-bs-members` gives
`BS_G = BS_(G_0) ⊆ B_A`. That theorem assumes only non-discreteness. So
`Γ_1 ∈ B_A`.

**Step 2b (commensurator discrete, `X ≠ H^2`).** The instances paragraph of
`commensurator-rigid-bs-classes-are-virtual-products` applies.
- By Mostow--Prasad, isometries may reverse orientation, and we work in `Isom(X)`.
- `Comm(G_0) ≅ Comm_(Isom(X))(G_0)`. This is a finite extension of the discrete
  `Comm_L(G_0)`, so it is discrete and contains `G_0` with finite index.
- `VZ(G_0) = 1` by Borel density.
- `G_0` is linear in characteristic zero, so it lies in `B_A` by
  `char-zero-linear-groups-satisfy-permutational-boone-higman`.
- Item 3 of that node, applied to the torsion-free `Γ_1`, gives `Γ_1 ∈ B_A`.

**Step 2c (`X = H^2`).** Handled without Step 1 by
`cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`.

**Step 3.** `B_A` is closed under finite-index overgroups (item 2 of
`boone-higman-type-a-class-closed-under-finite-extensions`), so `Γ ∈ B_A`.

**Which case occurs.** Case 2b needs a lattice with discrete commensurator. By
Margulis, together with arithmeticity (Margulis in higher rank; Corlette and
Gromov--Schoen for `Sp(n,1)` and `F_4^(-20)`), such lattices exist only for `H^n`,
`n >= 3`, and `CH^n`, `n >= 2`. This is not used in the proof, which covers both
cases unconditionally.

**Trust surface.** Cited, not re-read:
- Foertsch--Lytchak;
- Mostow--Prasad rigidity, including that every automorphism of `Isom(X)^0` is
  induced by an isometry;
- Borel density;
- linearity of lattices via the adjoint representation;
- the fact that a finite extension of a discrete subgroup is discrete.
