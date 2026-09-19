---
rg: 2
id: cat0-tree-factor-type-a-proof
kind: route
title: Split along the tree factor into a graph of fibre groups, then apply the faithful-member theorem for BS_G
target: cat0-groups-with-a-tree-factor-lie-in-type-a-class
requires: [bs-class-with-faithful-member-lies-in-type-a-class, free-generalized-bs-groups-have-type-a-overgroups, arithmetic-nsp-lattices-have-faithful-bs-members, product-of-two-trees-lattices-satisfy-permutational-boone-higman, char-zero-linear-groups-satisfy-permutational-boone-higman, boone-higman-type-a-class-closed-under-finite-extensions]
---

Write `γ = (γ_Y, γ_T)`. Let `T'` be the barycentric subdivision of `T`, on which
`Γ` acts without inversions. Midpoint stabilizers contain edge stabilizers with
index `<= 2`.

**Step 1 (Bass--Serre).** Let `C` be compact with `ΓC = Y × T`. Then `pr_T(C)`
meets finitely many vertices, so `Γ` has finitely many orbits of vertices of `T`,
and by local finiteness finitely many orbits of edges and of vertices of `T'`. So `Γ` is the
fundamental group of a finite graph of groups whose vertex and edge groups are the
stabilizers `Γ_x` (Serre, *Trees*, §I.5.4; standard, not re-read). `T` is locally
finite, so `[Γ_v : Γ_e] <= deg(v)` for `e ∋ v`, and every edge inclusion has finite
index.

**Step 2 (fibres).** `Γ_v` preserves the fibre `F_v = Y × {v} ≅ Y`, because
`γ_T v = v` for `γ ∈ Γ_v`. It acts properly, since `Γ` does.
- **Cocompactness.** Let `C` be compact with `ΓC = Y × T`. Then `pr_T(C)` meets
  finitely many vertices `w_1, ..., w_s`. For each `w_j ∈ Γv`, fix `g_j` with
  `g_j w_j = v`.
- If `x ∈ F_v` and `x = γk` with `k ∈ C`, then `pr_T(k) = γ^{-1}v = w_j` for some
  `j`, and `h = γ g_j^{-1}` fixes `v`.
- So `x = h g_j k`, and `F_v = Γ_v · ⋃_j g_j (C ∩ F_(w_j))`, a compact union.

So `Γ_v` is a CAT(0) group, hence finitely presented (Bridson--Haefliger III.Γ.1.1;
standard, not re-read). Edge and midpoint stabilizers have finite index in adjacent
vertex stabilizers, and `T` is connected, so all of them are abstractly
commensurable with `G = Γ_v`. Hence `Γ ∈ BS_G`, which is item 1. Item 2 is
`bs-class-with-faithful-member-lies-in-type-a-class`.

**Instance (a).** Let `Y = E^n`.
- **Degenerate `T`.** If every vertex of `T` has degree `<= 2`, then `T` is a
  finite path or a line; a ray has no cocompact isometry group.
  - For a line, `Γ` acts properly and cocompactly on `E^(n+1)`.
  - For a finite path, `Γ` preserves the fibre over its center, which may be the
    midpoint of an edge, and acts on it properly and cocompactly.
  - In both cases the fibre-group argument below shows that `Γ` is virtually free
    abelian, hence linear over `Z`, and
    `char-zero-linear-groups-satisfy-permutational-boone-higman` applies.
- **Product preservation.** Otherwise `T` has no Euclidean de Rham factor, and
  every isometry of `E^n × T` splits (de Rham decomposition, Foertsch--Lytchak;
  standard, not re-read). So the product hypothesis holds.
- **The fibre group.** `G` acts properly and cocompactly on `E^n`, so its image in
  `Isom(E^n)` is crystallographic with finite kernel. By Bieberbach it contains a
  finite-index `Z^n`. A finitely generated finite-by-`Z^n` group is virtually `Z^n`:
  pass to the finite-index centralizer of the finite kernel, a central extension of
  a free abelian group by a finite group. It is finitely generated nilpotent, hence
  virtually torsion-free, and a torsion-free finite-index subgroup maps isomorphically
  onto a finite-index subgroup of `Z^n`.
- So `G` is commensurable with `Z^n` and `BS_G = BS_(Z^n)`. The HNN extension of
  `Z^n` along `x ↦ 2x` is faithful on its tree, by BLIW Theorem 12.1 and its use in
  Theorem 12.3: the kernel lies in `⋂_i 2^i Z^n = 0`.
- For `n = 0`, `G` is finite and `Γ` is virtually free, so linear.

**Instance (b).** `G` is virtually free. If it is non-elementary, `BS_G = BS_(F_2)`,
and `free-generalized-bs-groups-have-type-a-overgroups` applies. If it is virtually
`Z`, `BS_G = BS_Z`, which is instance (a) with `n = 1`. This is the known node.

**Instance (c).** `BS_G = BS_Λ`, and instance 2 of
`arithmetic-nsp-lattices-have-faithful-bs-members` supplies the faithful member.
