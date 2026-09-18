---
rg: 2
id: commensurator-rigid-bs-products-proof
kind: route
title: The tree-fixing normal subgroup N has finite outer automorphism group, so a finite-index subgroup splits as N times its centralizer
target: commensurator-rigid-bs-classes-are-virtual-products
requires: [commensurator-rigid-groups-lack-faithful-bs-members, char-zero-linear-groups-satisfy-permutational-boone-higman, boone-higman-type-a-class-closed-under-finite-extensions]
---

**Step 0 (reduce to torsion-free vertex groups).** Let `H_1 ≤ H` be torsion-free of
finite index. `H_1` acts on the barycentric subdivision `T'` of the Bass--Serre tree
of `H` without inversions, with finitely many orbits.
- Its vertex stabilizers are finite-index subgroups of vertex or edge groups of `H`,
  so they are commensurable with `G` and torsion-free.
- Its edge inclusions have finite index.
- So `H_1 ∈ BS_G`, with Bass--Serre tree `T'` and torsion-free vertex groups.

**Step 1 (the normal subgroup).** Apply Steps 1--6 of
`commensurator-finite-no-faithful-bs-proof` to `H_1`. They give a nontrivial
`N ⊴ H_1` that equals `P_x ⊆ V_x` for every vertex group `V_x` of `H_1`, and has
finite index in each.
- `N` fixes `T'` pointwise, so `H` is not faithful. That is item 2.
- `H_1/N` acts on `T'` with finite vertex stabilizers `V_x/N` and finitely many
  orbits. So it is the fundamental group of a finite graph of finite groups, hence
  finitely generated and virtually free.

**Step 2 (finite outer action).** `N` is torsion-free and commensurable with `G`, so
`VZ(N) = 1` by Step 1 of the obstruction proof.
- **Aut(N) embeds in Comm(N).** Suppose an automorphism `α` of `N` agrees with the
  identity on a finite-index `N_0 ≤ N`. For `n ∈ N` and
  `x ∈ N_0 ∩ n^{-1} N_0 n`, applying `α` to `n x n^{-1}` gives
  `α(n) x α(n)^{-1} = n x n^{-1}`. So `n^{-1} α(n)` centralizes a finite-index
  subgroup, and `α(n) = n`.
- **Finite index.** `Comm(N) ≅ Comm(G)`. The image of `N` there is commensurable
  with the image of `G`, which has finite index. So
  `[Aut(N) : Inn(N)] <= [Comm(N) : im N] < ∞`, and `Out(N)` is finite.

**Step 3 (splitting).** Let `H_2` be the kernel of `H_1 → Out(N)`, a subgroup of
finite index.
- For `h ∈ H_2`, `conj_h|_N = conj_n` for a unique `n ∈ N`, and `h n^{-1}`
  centralizes `N`. So `H_2 = N · C_(H_2)(N)`.
- `N ∩ C_(H_2)(N) = Z(N) = 1`, and both factors are normal in `H_2`. So
  `H_2 ≅ N × C_(H_2)(N)`.
- `C_(H_2)(N) ≅ H_2/N ≤ H_1/N` is finitely generated and virtually free. That is
  item 1.

**Step 4 (item 3).** Suppose `G_0 ≤ G` has finite index and lies in `B_A`.
- `N` is commensurable with `G`, so a finite-index `N_0 ≤ N` embeds in `G_0`, and
  `N_0 ∈ B_A`.
- A finitely generated virtually free group is linear over `Z`, so `F ∈ B_A` by
  `char-zero-linear-groups-satisfy-permutational-boone-higman`.
- By items 1--2 of `boone-higman-type-a-class-closed-under-finite-extensions`,
  `N_0 × F ∈ B_A`, and so is its finite-index overgroup `H`.

**Instances.** Let `G` be a torsion-free lattice in `Isom(X)`, with `X` irreducible
and `X ≠ H^2`.
- Every isomorphism between finite-index subgroups of `G` is conjugation by an
  isometry of `X` (Mostow--Prasad; cited, not re-read). That isometry is unique,
  since a lattice has trivial centralizer. So `Comm(G) ≅ Comm_(Isom(X))(G)`.
- If `Comm_(Isom(X)^0)(G ∩ Isom(X)^0)` is discrete, then `Comm_(Isom(X))(G)` is
  discrete too. A discrete group containing a lattice contains it with finite index.
- `VZ(G) = 1` by Borel density.
- Lattices in `Isom(X)` are linear in characteristic zero, through the adjoint
  representation of `Isom(X)^0` and induction.
