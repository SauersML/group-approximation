---
rg: 2
id: discrete-factor-tree-lattice-splitting-proof
kind: route
title: A discrete factor makes its kernel cocompact on the other factors, whose normalizer is then discrete by a centralizer argument, which splits the lattice virtually as kernel times free
target: discrete-factor-tree-lattices-are-virtually-products
requires: [product-of-trees-lattices-with-faithful-factor-satisfy-pbh, product-of-two-trees-lattices-satisfy-permutational-boone-higman, boone-higman-type-a-class-closed-under-finite-extensions, bs-class-with-faithful-member-lies-in-type-a-class]
---

Notation as in the target. `pr'` is the map `Gamma_0 -> Aut(X_i')` to the other
factors, with kernel `K^c`. The kernel `Z` of `Gamma_0` on `X` lies in every
vertex stabilizer, so it is finite.

**Step 0 (finite kernels are trivial on X).** If `K_i` is finite, it fixes a
vertex of `X_i'`. For `j != i` its fixed set in `T_j` is a nonempty subtree,
invariant under `pr_j(Gamma_0)` because `K_i` is normal, so it is all of the
minimal tree `T_j`. Since `pr_i(K_i) = 1`, `K_i <= Z`.

**Step 1 (item 1).** A subgroup of `Aut(T_i)` is discrete iff its vertex
stabilizers are finite. `H_i / K_i` is the stabilizer of the vertex in
`pr_i(Gamma_0)`, so it is finite. By Lemma P (P1) of
`product-of-trees-faithful-factor-pbh-via-bass-serre-induction`, `H_i` acts on
`X_i'` factorwise with finite stabilizers and finitely many orbits, and so does
its finite-index subgroup `K_i`. By (P2), `K_i` is finitely presented.

**Step 2 (the image of `Gamma_0` on the other factors is discrete).** Fix a
vertex `x` of `X_i'`, and let `W` be its stabilizer in `pr'(Gamma_0)`, with
closure `W̄` (compact) in `Aut(X_i')`.
- `pr'(K_i)` is discrete (finite stabilizers) and normal in `pr'(Gamma_0)`, so
  its normalizer is closed and contains `W̄`.
- `W̄` acts by conjugation on the finitely generated group `pr'(K_i)`. Orbits
  of the finitely many generators are compact subsets of a discrete group, hence
  finite. So an open subgroup `W̄'` of finite index in `W̄` centralizes `pr'(K_i)`.
- Let `u ∈ W̄'`. Then `u` fixes `K_i · x` pointwise. That orbit is cobounded in
  `X_i'` (finitely many orbits), so for each `j != i` the projection
  `pr_j(K_i) x_j` is coarsely dense in `T_j`. In a leafless tree the convex hull
  of a coarsely dense vertex set is the whole tree: every vertex `v` lies on a
  bi-infinite line, and the geodesic between orbit points near the two far ends
  of that line passes through `v`. So `pr_j(u) = 1` for all `j != i`, and `u = 1`.
- Hence `W̄'` is trivial, `W̄` is finite, and `pr'(Gamma_0)` acts on `X_i'` with
  finite vertex stabilizers. It contains `pr'(K_i)`, which has finitely many
  vertex orbits, so `[pr'(Gamma_0) : pr'(K_i)]` is finite.

**Step 3 (splitting).** Put `Gamma_1 = pr'^(-1)(pr'(K_i))`, of finite index in
`Gamma_0`.
- For `gamma ∈ Gamma_1` pick `k ∈ K_i` with `pr'(k) = pr'(gamma)`. Then
  `k^(-1) gamma ∈ K^c`. So `Gamma_1 = K_i K^c`.
- Both factors are normal in `Gamma_0`, and `K_i ∩ K^c` acts trivially on `X`,
  so it lies in `Z`. Hence `[K_i, K^c] <= Z`.
- `K^c` acts on `T_i` with finite vertex stabilizers (they equal stabilizers of
  vertices of `X`), and `Gamma_1 / K_i ≅ K^c / (K^c ∩ K_i)` has finite index in
  `Gamma_0 / K_i ≅ pr_i(Gamma_0)`, which is discrete and acts on the locally
  finite tree `T_i` with finitely many orbits. So `K^c` is finitely generated and
  virtually free (Bass--Serre; standard, not re-read).
- Choose a free subgroup `F_1` of finite index in `K^c`. Since `F_1` is
  torsion-free and `Z` is finite, `F_1 ∩ Z = 1`.
- For `f ∈ F_1` and `k ∈ K_i` we have `f k f^(-1) = k z` with `z ∈ Z`. Fix a
  finite generating set `S` of `K_i`. Conjugation by `f` is determined by the
  tuple of such `z` for `s ∈ S`, so `F_1 -> Aut(K_i)` has finite image. Its kernel
  `F` has finite index in `F_1` and centralizes `K_i`.
- `K_i ∩ F <= Z ∩ F_1 = 1`, so `K_i F ≅ K_i x F`, and it has index at most
  `[K^c : F]` in `Gamma_1`. This is item 2 with `K' = K_i`.

**Step 4 (item 3).** `F` is finitely generated free. Free groups `F_k` lie in
`B_A`: `F_k` is a known faithful member case of
`bs-class-with-faithful-member-lies-in-type-a-class`, so `BS_(F_k) ⊆ B_A`, and
`F_k ∈ BS_(F_k)`. By item 1 of
`boone-higman-type-a-class-closed-under-finite-extensions`, `K_i x F ∈ B_A`
when `K_i ∈ B_A`. By item 2 of the same node, finite-index overgroups stay in
`B_A`, so `Gamma_0` and then `Gamma` lie in `B_A`.

**Three factors.** `K_i` acts on two trees with finite stabilizers and finitely
many orbits, by Step 1. If one of them has more than two ends,
`product-of-two-trees-lattices-satisfy-permutational-boone-higman` puts `K_i` in
`B_A`. Otherwise both are lines, `K_i` is virtually `Z^2`, and `Z^2 ∈ B_A` (the
scale-invariant case of `bs-class-with-faithful-member-lies-in-type-a-class`).

**Non-discrete factors.** If `pr_i(Gamma_0)` is not discrete, its vertex
stabilizers are infinite, so `[H_i : K_i]` is infinite. If moreover `K_i` is not
contained in `Z`, then by Step 0 it is infinite. This is the list in the target.
