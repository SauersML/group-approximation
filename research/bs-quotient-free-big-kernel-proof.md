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
  let `H_2 ≤ H_1` be the kernel, of finite index. Its elements act on `K` by inner
  automorphisms, so `H_2 = K · C` with `C = C_(H_2)(K)`.
  - `C ∩ K = Z(K)`, which may be infinite, and `C/Z(K) ≅ H_2/K ≤ H_1/K ≅ F_m` is free.
  - The central extension `1 → Z(K) → C → C/Z(K) → 1` splits over the free quotient,
    so `C = Z(K) × F` with `F` free.
  - Then `H_2 = K · F`, `F` centralizes `K`, and `K ∩ F ⊆ Z(K) ∩ F = 1`. So
    `H_2 ≅ K × F` exactly.
  - This is due to referee a, and replaces an earlier case split on `Z(K)`, which
    missed an infinite center.
- **Finite `Out(R(G))` (the separate statement in item 3).** `K ⊇ N ≅ R(G)` with
  finite index. `N` is characteristic
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
- **The action on `K`.** It is by conjugation, realized through the projection
  `p : Γ → Aut(T_1) × Aut(T_2)`. `Γ` acts faithfully on `T_1 × T_2 × T_3`, and `K`
  fixes `T_3`, so `p` is injective on `K`. `K` has finite index in the vertex
  stabilizer `Γ_v`, which acts on `T_1 × T_2` properly and cocompactly, so `p(K)` is
  a cocompact lattice in `Aut(T_1) × Aut(T_2)`.
- **Discrete projection.** If `p(Γ)` is discrete, it is a lattice containing the
  lattice `p(K)`, so `[p(Γ) : p(K)] = covol(p(K)) / covol(p(Γ)) < ∞`. Conjugation
  by `Γ` on `K` factors through `p(Γ)` and is inner on `p(K)`, so its image in
  `Out(K)` is finite. Conversely, an infinite image in `Out(K)` forces `p(Γ)`, and
  hence the normalizer of `p(K)`, to be non-discrete.

**Trust surface.** Standard, not re-read: that extensions by free groups split,
Bass--Serre theory, and that finitely generated virtually free groups are linear.
