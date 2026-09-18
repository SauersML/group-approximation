---
rg: 2
id: faithful-generalized-bs-witnesses-pass-to-direct-products-proof
kind: route
title: Glue the two product graphs of groups along one edge and intersect the two kernels
target: faithful-generalized-bs-witnesses-pass-to-direct-products
requires:
  - surface-groups-have-faithful-generalized-bs-witnesses
  - virtually-free-extensions-lie-in-generalized-bs-classes
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
  - free-generalized-bs-groups-have-type-a-overgroups
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

Let `H_A = π_1(Γ_A)` be a faithful witness for `A`, with vertex groups `A_v` and edge groups `A_e`,
and let `H_B = π_1(Γ_B)` be one for `B`, with `B_w` and `B_f`.

1. **Product graphs.** `Γ_A × B` is the graph `Γ_A` with vertex groups `A_v × B`, edge groups
   `A_e × B`, and edge maps `α_e × id_B`. Its fundamental group is `H_A × B`: every stable letter
   commutes with `B`, and `B` is identified across all edges. Its Bass–Serre tree is `T_A`, on which
   `B` acts trivially. So the kernel of `H_A × B` on `T_A` is exactly `1 × B`, because `H_A` is
   faithful. Likewise `A × Γ_B` has fundamental group `A × H_B`, tree `T_B`, and kernel `A × 1`.
2. **Glue.** Fix vertices `v` of `Γ_A` and `w` of `Γ_B`. Choose finite-index `A_0 ≤ A_v` and
   `A_1 ≤ A` with `A_0 ≅ A_1`, and finite-index `B_1 ≤ B` and `B_0 ≤ B_w` with `B_1 ≅ B_0`; these
   exist by commensurability. Join `v` to `w` by a new edge `ε` with group `A_0 × B_1`, included in
   `A_v × B` directly and in `A × B_w` through `A_0 × B_1 ≅ A_1 × B_0`. Call the result `Δ` and put
   `L = π_1(Δ)`. Every vertex and edge group is commensurable with `A × B`, and every inclusion has
   finite index, so `L ∈ BS_{A×B}`.
3. **Faithful.** `L` acts on its tree `T_L` without inversions, so its kernel `K` is the intersection
   of all edge stabilizers.
   - The subgraph `Γ_A × B` of `Δ` keeps its edge groups. So, as in BLIW Lemma 10.1, `T_A` embeds
     `H_A × B`-equivariantly in `T_L`.
   - An element of `L` fixing an edge of that copy of `T_A` lies in the corresponding conjugate of
     some `A_e × B ≤ H_A × B`. So `K ≤ H_A × B` acts trivially on `T_A`, and by step 1, `K ≤ 1 × B`.
   - Symmetrically, `K ≤ A × 1` inside `A × H_B`.
   - `K` also fixes the edge `ε`, so it lies in the edge group of `ε`. On the `v` side,
     `K ≤ (1 × B) ∩ (A_0 × B_1) = 1 × B_1`. Transported to the `w` side, `K ≤ 1 × B_0`, while also
     `K ≤ (A × 1) ∩ (A_1 × B_0) = A_1 × 1`. Hence `K = 1`.
   `L` is nontrivial, so it is a faithful witness for `A × B`.
4. **Item 3.** Faithful witnesses:
   - `Z^k`: BLIW Theorem 12.3's proof uses the HNN extension of `Z^k` by `x ↦ 2x`, which is faithful
     by strong scale invariance (Theorem 12.1).
   - `F_k`: the Burger–Mozes amalgam (Theorem 12.5 / 12.6).
   - Surface groups: `surface-groups-have-faithful-generalized-bs-witnesses`.

   Products of these are of type `F_∞`. So BLIW Theorem 11.1, applied for every `n` as in
   `surface-generalized-bs-groups-satisfy-boone-higman-proof`, gives type-`F_∞` simple envelopes
   for every member of `BS_G`. Extensions by virtually free groups are members by
   `virtually-free-extensions-lie-in-generalized-bs-classes`.

`free-generalized-bs-groups-have-type-a-overgroups` is required only for the `F_k` witness, which it
records from BLIW §12.
