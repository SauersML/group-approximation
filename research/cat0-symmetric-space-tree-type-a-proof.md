---
rg: 2
id: cat0-symmetric-space-tree-type-a-proof
kind: route
title: Split along the tree; a torsion-free fibre lattice either has a non-discrete commensurator, giving a faithful Hecke member, or forces a virtual product with a free group
target: cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class
requires: [cat0-groups-with-a-tree-factor-lie-in-type-a-class, arithmetic-lie-lattices-have-faithful-bs-members, commensurator-rigid-bs-classes-are-virtual-products, char-zero-linear-groups-satisfy-permutational-boone-higman, cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Product preservation.** If `T` has a branch point, `X × T` has no Euclidean
factor, and `X` and `T` are non-isometric irreducible factors. If `T` is a line,
`R` is the Euclidean de Rham factor. Either way isometries preserve the
decomposition (Foertsch--Lytchak; cited, not re-read). Otherwise it is a hypothesis.

**Simplicial action.** With a branch point, isometries of `T` preserve branch
vertices, and the vertices are exactly the points at integer distance from a branch
vertex, so `Γ` acts on `T` by tree automorphisms. Steps 1--3 assume this.

**Step 0 (`T` a line, any action).** Let `Γ` be virtually torsion-free.
- Properness makes the kernel of `Γ → Isom(X) × Isom(R)` finite. A torsion-free
  finite-index `Γ_1 ≤ Γ` therefore embeds.
- Let `Γ_2 ≤ Γ_1` be the finite-index subgroup mapping into
  `Isom(X)^0 × Isom(R)`.
- `Isom(X)^0` has trivial center, so its adjoint representation is faithful.
  `Isom(R) ≅ R ⋊ Z/2` embeds in `GL_2(R)` as affine maps.
- So `Γ_2` is a finitely generated subgroup of a real linear group, and
  `char-zero-linear-groups-satisfy-permutational-boone-higman` gives `Γ_2 ∈ B_A`.
- Item 2 of `boone-higman-type-a-class-closed-under-finite-extensions` gives
  `Γ ∈ B_A`.

This step is due to referee a, who pointed out that for `T = R` the translation
parts can be dense, for example `Γ = {(g, φ(g) + n)}` with `φ : G → R` of image
`Z + √2 Z`. Then `Γ` is not simplicial on `R`, and Step 1 does not apply.

**Step 1 (the fibre lattice).** By item 1 of
`cat0-groups-with-a-tree-factor-lie-in-type-a-class`, `Γ ∈ BS_G` with `G = Γ_v`.
`G` acts properly and cocompactly on `X × {v}`.
- `G` is virtually torsion-free by hypothesis. Let `G_0 ≤ G` be torsion-free of
  finite index, mapping into `Isom(X)^0`.
- `G_0` acts freely, hence faithfully, on `X`. So it is a torsion-free cocompact
  lattice in `L = Isom(X)^0`, which is simple with trivial center.
- `BS_G = BS_(G_0)`.

**Step 2a (commensurator non-discrete).** If `Comm_L(G_0)` is not discrete, the
theorem of `arithmetic-lie-lattices-have-faithful-bs-members` gives
`BS_(G_0) ⊆ B_A`. That theorem assumes only non-discreteness. So `Γ ∈ B_A`.

**Step 2b (commensurator discrete, `X ≠ H^2`).** By the instances paragraph of
`commensurator-rigid-bs-classes-are-virtual-products`, `G_0` satisfies its
hypotheses: Mostow--Prasad, the discreteness passing to `Isom(X)`, and Borel
density.
- `G_0` is linear in characteristic zero, so `G_0 ∈ B_A`
  (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
- Item 3 of that node gives `Γ ∈ B_A` for every member of `BS_(G_0)`, whatever its
  vertex groups.

**Step 2c (`X = H^2`).** `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`
handles it, without the torsion hypothesis.

**Which case occurs.** By Margulis, with arithmeticity (Margulis in higher rank;
Corlette and Gromov--Schoen for `Sp(n,1)` and `F_4^(-20)`), case 2b occurs only for
`H^n`, `n >= 3`, and `CH^n`, `n >= 2`. This is not used in the proof.

**Trust surface.** Cited, not re-read:
- Foertsch--Lytchak;
- Mostow--Prasad rigidity, including that every automorphism of `Isom(X)^0` is
  induced by an isometry;
- Borel density;
- linearity of lattices via the adjoint representation;
- the fact that a finite extension of a discrete subgroup is discrete.
