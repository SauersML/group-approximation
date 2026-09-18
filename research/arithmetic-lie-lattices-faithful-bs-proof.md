---
rg: 2
id: arithmetic-lie-lattices-faithful-bs-proof
kind: route
title: The kernel is discrete and normalized by a non-discrete group; its identity component centralizes the kernel and, by Borel density, contains a simple factor
target: arithmetic-lie-lattices-have-faithful-bs-members
requires: [bs-class-with-faithful-member-lies-in-type-a-class]
---

**Membership.** Each `c_i` commensurates `G`, so `G_i` and
`c_i G_i c_i^{-1} = G ∩ c_i G c_i^{-1}` have finite index in `G`. So `H` is the
fundamental group of a graph of groups with one vertex `G` and `r` loops, with edge
groups `G_i` and finite-index inclusions. It lies in `BS_G`.

**Step 1 (the kernel).** Let `K` be the kernel of `H` on its Bass--Serre tree. It is
the largest normal subgroup of `H` contained in `G`, so it is normal in `G`.
- For each `i`, `K = t_i^{-1} K t_i ⊆ G ∩ t_i^{-1} G t_i = G_i` by Britton's lemma.
- For `k ∈ K`, `t_i k t_i^{-1} = c_i k c_i^{-1}` holds in `G ⊆ L`, so
  `c_i K c_i^{-1} = t_i K t_i^{-1} = K`.
- So `D` normalizes `K` in `L`.

**Step 2 (a closed normalizer).** `K ⊆ G` is discrete, hence closed. Let
`N = N_L(K)`. If `g_j → g` in `L` with `g_j ∈ N`, then for `k ∈ K`,
`g_j k g_j^{-1} ∈ K` converges to `g k g^{-1}`, which lies in the closed set `K`.
The same argument for `g_j^{-1} → g^{-1}` gives `g ∈ N`. So `N` is closed, and it
contains `D̄`, the closure of `D`.

**Step 3 (a connected piece).** `D̄` is a closed, non-discrete subgroup of the Lie
group `L`. By Cartan's closed subgroup theorem it is a Lie subgroup of positive
dimension, so its identity component `D̄°` is nontrivial.
- For `k ∈ K`, the map `D̄° → K`, `g ↦ g k g^{-1}`, is continuous from a connected
  space to a discrete one, so it is constant. So `D̄°` centralizes `K`.
- `D̄°` is normal in `D̄ ⊇ G`, so its Lie algebra `d ≠ 0` is `Ad(G)`-invariant.
- By Borel density, `G` is Zariski dense in `L`, which has no compact factors. So
  `d` is `Ad(L)`-invariant, that is, an ideal of `Lie(L)`.
- A nonzero ideal of a semisimple Lie algebra contains a simple ideal `l_j`. So
  `D̄°` contains the simple factor `L_j`, which therefore centralizes `K`.

**Step 4 (K = 1).** `L` has trivial center, so `L = L_1 × ... × L_k` with each
`L_i` simple with trivial center, and `Z_L(L_j) = ∏_(i≠j) L_i`.
- `K ⊆ G ∩ ∏_(i≠j) L_i`, which is finite: trivially for `k = 1`, and
  because `G` is irreducible for `k >= 2`. Then `K` is a finite normal subgroup of `G`. Its normalizer in `L` is
  Zariski closed and contains `G`, so it is all of `L`. The connected group `L`
  then centralizes the finite group `K`, and `K ⊆ Z(L) = 1`.

This proves the lemma.

**Step 5 (the theorem).** Suppose `Comm_L(G)` is not discrete.
- **Countability.** `Comm_L(G)` is countable. An element `c` is determined by the
  isomorphism `G_c → cG_cc^{-1}` it induces between finite-index subgroups of `G`:
  two elements inducing the same isomorphism differ by an element centralizing the
  Zariski-dense `G_c`, which is central, hence trivial. `G` is finitely generated,
  so there are countably many such isomorphisms.
- **The chain.** Enumerate `Comm_L(G) = {c_1, c_2, ...}` and put
  `D_r = ⟨G, c_1, ..., c_r⟩`. Suppose every `D_r` is discrete. Then each `D_r`
  contains the lattice `G`, so `[D_r : G] = covol(G)/covol(D_r)`.
- **Kazhdan--Margulis.** Covolumes of lattices in `L` are bounded below by a
  constant `ε > 0`. So the increasing chain `G <= D_1 <= D_2 <= ...` has index at
  most `covol(G)/ε` and stabilizes. Then `Comm_L(G) = ⋃ D_r = D_r` is discrete, a
  contradiction.
- So some `D_r` is non-discrete, and the lemma applies with `c_1, ..., c_r`.
- **Transfer to `G'`.** `BS_G` depends only on the abstract commensurability class
  of `G`, and `G` is finitely presented, as a lattice in a semisimple Lie group
  (standard). `bs-class-with-faithful-member-lies-in-type-a-class` gives
  `BS_(G') = BS_G ⊆ B_A`.

**Instances.**
- **Instance 1.** Let `A` be the quaternion algebra over `Q` ramified at `{2, 3}`,
  and `O` a maximal order. `O^1/±1` is a cocompact arithmetic Fuchsian group, and
  it has a torsion-free finite-index subgroup (Selberg), which is a closed surface
  group of some genus `g_0 >= 2`. Arithmetic lattices have dense commensurator
  (Borel).
- **Instance 2.** A finite-index torsion-free subgroup of `PSL_2(Z)` is a free
  group, commensurable with every `F_k`, `k >= 2`. `PSL_2(Q)` commensurates it and
  is dense in `PSL_2(R)`.
- **Instance 3.** The standard arithmetic lattices are arithmetic by definition.
- **Instance 4.** The higher-rank case rests on Margulis arithmeticity.

**Trust surface.** Cited and not re-read:
- Britton's lemma;
- Cartan's closed subgroup theorem;
- Borel density;
- the Kazhdan--Margulis covolume bound;
- finite presentation of lattices;
- Borel's density of the commensurator of arithmetic groups, and Margulis's
  commensurator and arithmeticity theorems;
- the finiteness of `G ∩ ∏_(i≠j) L_i` for irreducible lattices;
- Selberg's lemma.
