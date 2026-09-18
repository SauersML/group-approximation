---
rg: 2
id: commensurator-rigid-bs-products-proof
kind: route
title: The tree kernel has finite outer automorphism group, so a finite-index subgroup is the kernel times a free subgroup of its centralizer
target: commensurator-rigid-bs-classes-are-virtual-products
requires: [commensurator-rigid-groups-have-no-faithful-bs-members, char-zero-linear-groups-satisfy-permutational-boone-higman, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Step 1 (the kernel).** Let `v` be a vertex.
- By `commensurator-rigid-groups-have-no-faithful-bs-members`, some finite-index
  subgroup of `G_v` acts trivially on the tree, so it lies in `K`.
- `K ⊆ G_x` for every vertex `x`, so `K` has finite index in `G_v`. Every vertex
  stabilizer `G_x` is a conjugate of one of the finitely many vertex groups, and `K`
  is normal in `H`, so `[G_x : K] < ∞` at every vertex of the tree. `K` is
  commensurable with `G`. That is item 1.
- `K` is finitely generated, like `G_v`.
- `H/K` acts on the tree with vertex stabilizers `G_x / K`, finite by the previous
  point, and finitely many orbits.
  So it is the fundamental group of a finite graph of finite groups, finitely
  generated and virtually free.

**Step 2 (VZ(K) is finite).** Choose a finite-index `U ≤ K` isomorphic to a
finite-index subgroup `U'` of `G`.
- `VZ(K) ∩ U = VZ(U) ≅ VZ(U') ⊆ VZ(G) = 1`. Here an element of `U` centralizes a
  finite-index subgroup of `K` if and only if it centralizes one of `U`.
- So `VZ(K)` injects into `K/U` and is finite.

**Step 3 (Out(K) is finite).** Consider `κ : Aut(K) → Comm(K)`.
- **Finite kernel.** Suppose `α` agrees with the identity on a finite-index
  `K_0 ≤ K`. For `n ∈ K` and `x ∈ K_0 ∩ n^{-1} K_0 n`, applying `α` to `n x n^{-1}`
  gives `α(n) x α(n)^{-1} = n x n^{-1}`. So `n^{-1} α(n) ∈ VZ(K)`. Hence `α` is
  determined by the values `n^{-1}α(n) ∈ VZ(K)` on a finite generating set, and
  `ker κ` is finite.
- **Finite-index image of `Inn(K)`.** `κ(Inn(K))` is the image of `K` in
  `Comm(K) ≅ Comm(G)`. It is commensurable with the image of `G`, which has finite
  index. So `κ(Inn(K))` has finite index in `Comm(K)`.
- So `[Aut(K) : Inn(K)] <= |ker κ| · [Comm(K) : κ(Inn(K))] < ∞`.

**Step 4 (splitting).** Let `H_2` be the kernel of `H → Out(K)`, a subgroup of
finite index.
- For `h ∈ H_2`, `conj_h|_K = conj_k` for some `k ∈ K`, and `h k^{-1}` centralizes
  `K`. So `H_2 = K · C` with `C = C_(H_2)(K)`, and `K ∩ C = Z(K) ⊆ VZ(K)`, which is
  finite.
- `C/Z(K) ≅ H_2/K` is finitely generated and virtually free. Let `Φ ≤ C/Z(K)` be
  free of finite index, and let `C_1` be its preimage.
- The central extension `1 → Z(K) → C_1 → Φ → 1` splits because `Φ` is free. Let
  `F ≤ C_1` be the image of a splitting.
- `F` is free, commutes with `K`, and `F ∩ K ⊆ F ∩ Z(K) = 1`. So `K × F ≅ KF ≤ H_2`,
  and `[H_2 : KF] <= [C : F] < ∞`. That is item 2.

**Step 5 (item 3).** `K` is commensurable with `G`.
- If `G_0 ≤ G` has finite index and lies in `B_A`, then some finite-index `K_0 ≤ K`
  embeds in `G_0`, so `K_0 ∈ B_A`.
- `F` is linear over `Z`, so `F ∈ B_A` by
  `char-zero-linear-groups-satisfy-permutational-boone-higman`.
- By items 1--2 of `boone-higman-type-a-class-closed-under-finite-extensions`,
  `K_0 × F ∈ B_A`, and so is its finite-index overgroup `H`.

**Instances.** Let `X` be irreducible, `X ≠ H^2`, and `G` a torsion-free lattice in
`Isom(X)`.
- By Mostow--Prasad, every isomorphism between finite-index subgroups is
  conjugation by a unique isometry, possibly orientation-reversing; the
  centralizer of a lattice is trivial.
- So `Comm(G) ≅ Comm_(Isom(X))(G)`. If the commensurator in `Isom(X)^0` is
  discrete, so is this finite extension, and it contains `G` with finite index.
- `VZ(G) = 1` by Borel density.
- `G` is linear in characteristic zero, through the adjoint representation and
  induction.

**Trust surface.** Cited and not re-read: Mostow--Prasad rigidity, Borel density,
and the Bass--Serre structure theorem.
