---
rg: 2
id: bs-quotient-free-big-kernel-proof
kind: route
title: Finite residuals are characteristic, lie in every finite-index subgroup, and are carried onto each other by the edge maps
target: bs-classes-over-virtually-quotient-free-groups-have-big-kernels
requires: [cat0-groups-with-a-tree-factor-lie-in-type-a-class, product-of-two-trees-lattices-satisfy-permutational-boone-higman, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Step 1 (finite residuals are commensurability invariants).** Let `U ≤ V` have
finite index.
- If `W ≤ U` has finite index in `U`, it has finite index in `V`. So `R(V) ⊆ R(U)`.
- Conversely, let `W ≤ V` have finite index. Then `W ∩ U` has finite index in `U`,
  so `R(U) ⊆ W ∩ U ⊆ W`. Hence `R(U) ⊆ R(V)`.
- So `R(U) = R(V)` for every finite-index `U ≤ V`.
- Isomorphisms preserve `R`. So if `V` is commensurable with `G`, then
  `R(V) ≅ R(G)` and `[V : R(V)] < ∞`: it equals `R` of a finite-index subgroup
  isomorphic to one of `G`, and `R(G)` has finite index in that subgroup.

**Step 2 (one subgroup in H).** Let `V_x`, `E_e`, `α_e`, `ω_e` be the graph of
groups of `H`.
- By Step 1, `R(E_e)` equals `R(V_(o(e)))` under `α_e`, since `α_e(E_e)` has finite
  index. Likewise `R(E_e)` equals `R(V_(t(e)))` under `ω_e`. Isomorphisms carry
  finite residuals onto finite residuals.
- So `α_e(R(E_e)) = R(V_(o(e)))` and `ω_e(R(E_e)) = R(V_(t(e)))`.
- **Tree edges.** For `e` in a maximal tree, `α_e(a) = ω_e(a)` in `H`, so
  `R(V_(o(e))) = R(V_(t(e)))` as subgroups of `H`. So all `R(V_x)` equal one subgroup
  `N`.
- **Other edges.** For each remaining edge, `t_e N t_e^{-1} = ω_e(R(E_e)) = N`.
- `N` is characteristic in each `V_x`, hence normalized by `V_x`. So `N ⊴ H`.
- `N` lies in every vertex group, so it fixes the tree, and `N ⊆ K`. By Step 1, `N`
  has finite index in each `V_x`. That is item 1.

**Step 3 (items 2 and 3).**
- `H/K` acts on the tree with finite vertex stabilizers and finitely many orbits.
  So it is the fundamental group of a finite graph of finite groups, finitely
  generated and virtually free.
- **Item 2.** Let `F_m ≤ H/K` be free of finite index, with preimage `H_1`. The
  extension `1 → K → H_1 → F_m → 1` splits because `F_m` is free, so
  `H_1 = K ⋊ F_m`.
- **Splitting off the free group.** If the image of `H_1` in `Out(K)` is finite,
  let `H_2 ≤ H_1` be the kernel. Its elements act on `K` by inner automorphisms,
  and `H_2 = K · C_(H_2)(K)`.
- **When `Z(K)` is trivial.** Then `H_2 ≅ K × C_(H_2)(K)`, and `C_(H_2)(K) ≅ H_2/K`
  is virtually free.
- **When `Z(K)` is finite.** The splitting argument of
  `commensurator-rigid-bs-products-proof`, Step 4, gives a free `F` with `K × F`
  of finite index.
- **Finite `Out(R(G))`.** `K ⊇ N ≅ R(G)` with finite index. `N` is characteristic
  in the vertex groups and normal in `H`, so `H` acts on `N`. If `Out(N)` is finite
  and `Z(N) = 1`, a finite-index `H_3 ≤ H` acts on `N` by inner automorphisms, and
  `H_3 = N · C` with `C = C_(H_3)(N)` and `N ∩ C = Z(N) = 1`, so `H_3 ≅ N × C`.
  - `C ∩ V_x ⊆ C_(V_x)(N)`, which embeds in `V_x / N` since `Z(N) = 1`. So `C` acts
    on the tree with finite stabilizers.
  - `N` fixes the tree, so `C`-orbits are `H_3`-orbits, finitely many.
  - So `C` is finitely generated and virtually free.
- **The `B_A` conclusion.** `K` is commensurable with `G`, so a finite-index
  subgroup of `K` lies in `B_A` when one of `G` does. Finite direct products,
  finite-index overgroups (`boone-higman-type-a-class-closed-under-finite-extensions`)
  and free groups (linear) finish item 3.

**Three trees.**
- **The fibre.** `G` acts on `T_1 × T_2` with finite stabilizers and finitely many
  orbits, so it lies in `B_A` by
  `product-of-two-trees-lattices-satisfy-permutational-boone-higman` (one factor
  with more than two ends).
- **The action on `K`.** It is by conjugation, realized through the projection of
  `Γ` to `Aut(T_1) × Aut(T_2)`. `K` acts on `T_1 × T_2` cocompactly with finite
  kernel.
- **Discrete projection.** If the projection is discrete, it contains the image of
  `K` with finite index, and the image in `Out(K)` is finite up to the finite kernel.

**Trust surface.** Standard, not re-read: that extensions by free groups split,
Bass--Serre theory, and that finitely generated virtually free groups are linear.
