---
rg: 2
id: faithful-hecke-members-products-proof
kind: route
title: The kernel of a product Hecke member projects to invariant normal subgroups of each factor
target: faithful-hecke-members-pass-to-direct-products
requires: [arithmetic-lie-lattices-have-faithful-bs-members, arithmetic-nsp-lattices-have-faithful-bs-members, bs-class-with-faithful-member-lies-in-type-a-class, cat0-groups-with-a-tree-factor-lie-in-type-a-class]
---

**Criterion.** Let `K` be the kernel of `H = H(G, φ)` on its Bass--Serre tree. It
is the largest normal subgroup of `H` contained in the vertex group `G`.
- **The kernel satisfies the conditions.** By Britton's lemma,
  `K = t_j^{-1} K t_j ⊆ G ∩ t_j^{-1} G t_j = A_j`, and
  `φ_j(K) = t_j K t_j^{-1} = K`. It is normal in `G`.
- **Any such `N` lies in the kernel.** Let `N` be normal in `G`, with `N ⊆ A_j` and
  `φ_j(N) = N` for all `j`. Then `t_j N t_j^{-1} = φ_j(N) = N`. For `n ∈ N`, write
  `n = φ_j(m)` with `m ∈ N`; then `t_j^{-1} n t_j = m ∈ N`. So `N` is normal in `H`,
  and `N ⊆ K`.

**Products.** Let `N ⊆ G_1 × G_2` be normal and invariant for the product data, and
let `π_1` be the projection to `G_1`.
- `π_1(N)` is normal in `G_1`, by conjugating with elements `(g, 1)`.
- `N ⊆ A_j × G_2` gives `π_1(N) ⊆ A_j`.
- `(φ_j × id)(N) = N` gives `φ_j(π_1(N)) = π_1(N)`.
- By the criterion for `(G_1, φ)`, `π_1(N) = 1`. In the same way `π_2(N) = 1`, so
  `N = 1`.
- Each new domain has finite index, and so does each image. By induction the same
  holds for any finite product.

**Consequence.**
- **Faithful data on each factor.**
  - For `Z^n`, the data `x ↦ 2x` on `Z^n` is faithful. An invariant `N` satisfies
    `N = 2N`, so `N ⊆ ⋂_i 2^i Z^n = 0`.
  - For arithmetic lattices, the lemma of `arithmetic-lie-lattices-have-faithful-bs-members`
    gives faithful one-vertex data `(G_i ∩ c^{-1}G_i c, Ad c)`.
  - For quaternion lattices on two trees, the one-letter data of
    `arithmetic-nsp-lattices-have-faithful-bs-members` is faithful.
- **Passing to `G`.** The product `P = G_1 × ... × G_m` is finitely presented and
  has faithful Hecke data. `G` is commensurable with `P`, so `BS_G = BS_P`, and
  `bs-class-with-faithful-member-lies-in-type-a-class` gives `BS_G ⊆ B_A`.
- **Reducible arithmetic lattices.** Such a lattice is commensurable with a product
  of irreducible arithmetic lattices in the factors (standard; not re-read).
- **The CAT(0) statement** is item 2 of `cat0-groups-with-a-tree-factor-lie-in-type-a-class`.

**Trust surface.** Britton's lemma, and the decomposition of reducible lattices up to
commensurability. Both are standard and not re-read.
