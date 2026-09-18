---
rg: 2
id: cat0-hyperbolic-plane-tree-type-a-proof
kind: route
title: The fibre group is virtually a surface group or commensurable with an arithmetic lattice; feed it to the tree-factor theorem
target: cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class
requires: [cat0-groups-with-a-tree-factor-lie-in-type-a-class, arithmetic-lie-lattices-have-faithful-bs-members, char-zero-linear-groups-satisfy-permutational-boone-higman]
---

**Item 1.**
- **Degenerate `T`.** If every vertex of `T` has degree `<= 2`, `T` is a line or a
  finite path. Then `Γ` acts geometrically on `H^2 × R`, and is virtually `S × Z` for a closed
  surface group `S` (Scott, *The geometries of 3-manifolds*, for `H^2 × R`;
  cited, not re-read). Or `Γ` preserves one fibre `H^2` (over the center of the
  path, possibly a midpoint) and acts on it geometrically, and the fibre argument
  below shows it is virtually a surface group. Either way `Γ` is linear over `Z`, and
  `char-zero-linear-groups-satisfy-permutational-boone-higman` applies.
- **Product preservation.** Otherwise `T` has a branch point, so `H^2 × T` has no
  Euclidean factor and its two factors are non-isometric irreducibles. Every
  isometry preserves the decomposition (Foertsch--Lytchak de Rham theorem; cited,
  not re-read).
- **The fibre group.** By item 1 of `cat0-groups-with-a-tree-factor-lie-in-type-a-class`,
  `Γ ∈ BS_G`, where `G = Γ_v` acts properly and cocompactly on
  `H^2 × {v}` (it preserves this fibre because `γ_T v = v`).
  - The image `Q` of `G` in `Isom(H^2)` is a cocompact Fuchsian group, and the
    kernel `F` is finite.
  - `Q` has a torsion-free finite-index surface subgroup `S` (Selberg); let `E` be
    its preimage.
  - The centralizer `C = C_E(F)` has finite index in `E`, and `C ∩ F = Z(F)`. So
    `C` is a central extension `1 → A → C → S' → 1` with `A` finite abelian and
    `S'` a finite-index subgroup of `S`, hence a closed orientable surface group.
  - Its class lies in `H^2(S'; A) ≅ A`. Restriction to a cover `S''` of degree
    `|A|` multiplies `H^2(-; A)` by the degree, so the class dies and the extension
    splits over `S''`.
  - So `G` contains a finite-index subgroup isomorphic to a surface group of genus
    `>= 2`: `S''` is non-elementary.
- **Conclusion.** By instance 1 of `arithmetic-lie-lattices-have-faithful-bs-members`,
  `BS_G ⊆ B_A`. So `Γ ∈ B_A`.

**Item 2.** `Γ ∈ BS_G` with `G = Γ_v`, by the same tree-factor node.
- The kernel `F` of `G → Isom(X)` is finite, since the action is proper. `G` is
  residually finite, so some finite-index `G_0 <= G` meets `F` trivially. Then
  `G_0` maps isomorphically onto a finite-index subgroup of the lattice
  `Q = im(G)`.
- Pass to `L = Isom(X)^0`, the connected semisimple group with trivial center and
  no compact factors. `Q ∩ L` has finite index in `Q` and is an arithmetic lattice
  in `L`.
- `Q ∩ L` is irreducible by hypothesis, so
  `arithmetic-lie-lattices-have-faithful-bs-members` gives `BS_G = BS_(Q ∩ L) ⊆ B_A`.
  The reducible case would need a product version of the faithful-member theorem,
  which is not proved here.

**Trust surface.** Cited, not re-read: the Foertsch--Lytchak splitting, Selberg's
lemma, `H^2` of closed orientable surfaces and the degree formula for restriction,
Scott's classification of `H^2 × R` lattices, and Margulis arithmeticity.
