---
rg: 2
id: micro-supported-tree-actions-self-embed-rigid-stabilizers
kind: claim
title: In a minimal general-type tree action with one nontrivial half-tree rigid stabilizer, every rigid stabilizer contains an infinite direct sum of copies of itself, so every (P_k) simplicity engine with nontrivial fixators leaves all bounded-rank host classes
distinct_from:
  tits-independence-amalgams-force-self-product-edge-groups: that treats one amalgam with the edge-product property and finds V x V inside the edge factor V by nesting conjugates at the two ends of the edge; this treats every faithful minimal general-type action on any tree, for every half-tree at once, with no independence hypothesis, gets infinite direct sums by hyperbolic ping-pong, and covers Banks--Elder--Willis (P_k).
  finite-cd-groups-have-no-micro-supported-line-action: that bounds disjointly supported rigid stabilizers of actions on the line by cd; this is the tree analogue, where micro-support forces unboundedly many disjoint copies of one rigid stabilizer.
  tits-independence-vertex-groups-are-branch-type: that uses local finiteness and (P) to show vertex stabilizers are branch-type groups; this uses no local finiteness and no product decomposition of stabilizers.
---

**ESTABLISHED (unreviewed).** Proof: `micro-supported-tree-actions-self-embed-rigid-stabilizers-proof`.

**Setting.** A group `Γ` acts faithfully and without inversions on a tree `T`
(any valence). For an oriented edge `f = (x, y)`, the **half-tree** `Y_f` is the
set of vertices whose geodesic to `x` passes through `y`. Its complement is
`Y_{f̄}`. The **rigid stabilizer** of a half-tree `Y` is
`R(Y) = {g ∈ Γ : g fixes every vertex outside Y}`. Assume:

- **(M)** the action is minimal, fixes no end, and `T` is not a line;
- **(N)** `R(Y_0) ≠ 1` for at least one half-tree `Y_0`.

**Theorem.**

1. **Transport.** For all half-trees `X`, `Y` there is `γ ∈ Γ` with `γX ⊆ Y`.
   Hence `R(X)` embeds in `R(Y)` by conjugation, and `R(Y) ≠ 1` for every
   half-tree `Y`. The action is micro-supported.
2. **Self-embedding.** Every half-tree `Y` contains infinitely many pairwise
   disjoint half-trees `Z_1, Z_2, ...`. So `⊕_{i ∈ N} R(Y)` embeds in `R(Y)`,
   and `R(Y)` is infinite.
3. **Abelian witnesses.** `Γ` and every overgroup of any `R(Y)`, including
   `Γ⁺ = ⟨Γ_f : f an edge⟩`, contain `⊕_N Z` or `⊕_N Z/p` for some prime `p`.
4. **Class-killing corollary.** No group `H` in which finite subgroups have
   bounded order and free abelian subgroups have bounded rank contains `R(Y)`.
   The excluded classes include finite groups, hyperbolic groups, groups of
   finite vcd and proper cocompact CAT(0) groups. So does every group whose abelian
   subgroups are all finitely generated. So no such group carries a faithful
   action satisfying (M) and (N).
5. **Independence engines.** Suppose that for some `k ≥ 1`, `Γ` has property
   `(P_k)` of Banks--Elder--Willis in the form
   `Fix(N) = Fix(N ∪ Y_f) · Fix(N ∪ Y_{f̄})`, where `N` is the set of vertices within
   distance `k−1` of an edge `f`. For `k = 1` this is Tits' property (P). Suppose
   also that some such `Fix(N)` is nontrivial and (M) holds. Then (N) holds, so
   items 1--4 apply. The Tits and Banks--Elder--Willis simplicity theorems give
   simple groups `Γ⁺` or `Γ^{+k}` only when those groups are nontrivial. So every host
   they produce, and every group those hosts are built from, lies outside the
   classes in item 4.

**Calibration.**

- `Aut(T_d)`, `d ≥ 3`, satisfies (M), (P) and (N), and `R(Y)` contains
  `⊕_N Z/2`, as item 3 requires.
- A free product `A * B` of finite groups acting on its Bass--Serre tree has
  trivial edge stabilizers, so (N) fails, and it is virtually free.
- Irreducible Burger--Mozes lattices are torsion-free of cohomological
  dimension 2. By item 4, the action on each factor tree, which satisfies (M),
  has every half-tree rigid stabilizer trivial.
- Excluding the line in (M) loses nothing: on a line, an automorphism that fixes
  a half-line pointwise is trivial, so (N) always fails there.

**Use for `boone-higman-conjecture`.** A Tits-type route embeds a decidable `G` in
a finitely presented `Γ` with (P) or (P_k) and takes `Γ⁺`. By item 5 the edge
fixators of `Γ` must contain infinite direct sums of copies of themselves, as in
Thompson-like or branch groups. No geometric or finite-dimensional group can
serve. `tits-independence-vertex-groups-are-branch-type` pins down
the locally finite case.

**Credit.** Transport of half-trees by hyperbolic elements is standard in the
theory of micro-supported actions (compare Caprace--Le Boudec on rigid
stabilizers). The self-embedding and the class-killing use are recorded here for
the Boone--Higman engines.
