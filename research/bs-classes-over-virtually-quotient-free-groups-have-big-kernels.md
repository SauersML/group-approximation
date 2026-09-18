---
rg: 2
id: bs-classes-over-virtually-quotient-free-groups-have-big-kernels
kind: claim
title: If the finite residual of G has finite index, every member of BS_G has a tree kernel of finite index in its vertex groups, and is virtually the kernel semidirect a free group
distinct_from:
  commensurator-rigid-groups-have-no-faithful-bs-members: that gets a large kernel from commensurator rigidity; this gets it from the opposite extreme, groups with essentially no finite quotients, with no hypothesis on the commensurator.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that records the authors' residual-finiteness obstruction to faithful members; this is its extreme form and identifies what remains, a semidirect product with a free group.
  product-of-trees-lattices-satisfy-permutational-boone-higman: that is open for lattices in three or more trees; this reduces the case with a virtually simple fibre to lattices of the form K ⋊ F_m.
---

**ESTABLISHED** through `bs-quotient-free-big-kernel-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Notation.** `R(V)` is the finite residual of a group `V`: the intersection of all
finite-index subgroups.

**Theorem.** Let `G` be a group with `[G : R(G)] < ∞`, for example virtually an
infinite simple group or virtually a group with no nontrivial finite quotients. Let
`H ∈ BS_G`, with tree kernel `K`. Then:
1. `R(V_x)` has finite index in each vertex group `V_x`. The subgroups `R(V_x)`,
   taken in `H`, are all equal, so `K ⊇ R(V_x)` has finite index in each `V_x`. In
   particular no member of `BS_G` is faithful.
2. `H/K` is finitely generated and virtually free, and `H` has a finite-index
   subgroup `K ⋊ F_m` with `F_m` free.
3. If the conjugation action of `H` on `K` has finite image in `Out(K)`, then `H` is
   virtually `K × F_m`. For example, this happens when `Out(R(G))` is finite and
   `R(G)` has trivial center. If moreover a finite-index subgroup of `G` lies in
   `B_A`, then `H ∈ B_A`.

**Application to three trees.** Let `Γ` be a lattice in `T_1 × T_2 × T_3`
preserving the factors. Suppose its stabilizer `G` of a vertex of `T_3`, a lattice
in `T_1 × T_2`, has finite-index finite residual. This is the typical
non-residually-finite fibre, for instance commensurable with a simple
Burger--Mozes or Wise lattice.
- By `cat0-groups-with-a-tree-factor-lie-in-type-a-class`, item 1, `Γ ∈ BS_G`, so `Γ`
  is virtually `K ⋊ F_m`, with `K` commensurable with `G`.
- If the image of `Γ` in `Out(K)` is finite, which holds when the projection of `Γ`
  to `Aut(T_1) × Aut(T_2)` is discrete, then `Γ` is virtually `K × F_m`. Then
  `Γ ∈ B_A` by `product-of-two-trees-lattices-satisfy-permutational-boone-higman`,
  whenever one of `T_1`, `T_2` has more than two ends.
- **Exact remaining gap for such `Γ`.** `F_m` acts on `K` through an infinite
  subgroup of `Out(K)`, realized by a non-discrete normalizer of `K` in
  `Aut(T_1) × Aut(T_2)`. `K ⋊ F_m` is again a lattice in three trees, so this is a
  reduction of shape, not a proof.
