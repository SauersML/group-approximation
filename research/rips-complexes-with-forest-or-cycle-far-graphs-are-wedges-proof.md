---
rg: 2
id: rips-complexes-with-forest-or-cycle-far-graphs-are-wedges-proof
kind: route
title: "Proof: independence complexes of disjoint unions of trees and cycles are points or wedges of spheres"
target: rips-complexes-with-forest-or-cycle-far-graphs-are-wedges
requires: []
---

A clique of the graph `d ≤ r` is exactly an independent set of `H = H_r(X)`,
so `R_r(X) = Ind(H)`.

**Tools.**

1. *Joins.* `Ind(A ⊔ B) = Ind(A) * Ind(B)`. A join with a contractible space
   is contractible. The join of two wedges of spheres is a wedge of spheres,
   since `P * Q ≃ Σ(P ∧ Q)` and smash products and suspensions of wedges of
   spheres are wedges of spheres. So it suffices to treat one component.
2. *Fold lemma.* If `u ≠ v` and `N(u) ⊆ N(v)`, then `Ind(H) ≃ Ind(H − v)`.
   Proof: in `Ind(H)` the link of `v` is `Ind(H − N[v])`. Every independent
   set of `H − N[v]` extends by `u`, because `u ∉ N[v]` (if `u ∈ N(v)` then
   `v ∈ N(u) ⊆ N(v)`, impossible) and `u` has no neighbour outside `N(v)`. So
   the link is a cone with apex `u`, and deleting `v` is a homotopy
   equivalence.
3. *Cofibre sequence.* For a vertex `v`,
   `Ind(H) = Ind(H − v) ∪ (v * Ind(H − N[v]))`, so there is a cofibre sequence
   `Ind(H − N[v]) → Ind(H − v) → Ind(H)`. If the first map is null-homotopic,
   `Ind(H) ≃ Ind(H − v) ∨ Σ Ind(H − N[v])`.

**Isolated vertex.** `Ind` of a single vertex is a point.

**Trees.** By induction on the number of vertices. Let `T` be a tree with at
least two vertices, `u` a leaf and `w` its neighbour. Every other neighbour
`v` of `w` satisfies `N(u) = {w} ⊆ N(v)`, so folding removes all of them.
What remains is the edge `u−w` together with a forest `F` (the pieces cut
off, minus the removed vertices). Then `Ind = S^0 * Ind(F)`: contractible if
`Ind(F)` is, otherwise the suspension of a sphere or of a point-or-sphere join,
which by tool 1 and induction is a point or a sphere. (For the empty forest,
`Ind` is the empty complex, whose join with `S^0` is `S^0`.)

**Paths.** As a check, the leaf step gives `Ind(P_n) ≃ Σ Ind(P_{n−3})`, with
`Ind(P_1) = pt`, `Ind(P_2) = S^0` and `Ind(P_3) ≃ S^0`. So `Ind(P_n)` is
contractible for `n ≡ 1 (mod 3)`, `≃ S^{k−1}` for `n = 3k` and for
`n = 3k − 1`.

**Cycles.** `Ind(C_3)` is three points, `S^0 ∨ S^0`. For `n ≥ 4`, tool 3 at a
vertex `v` gives `Ind(P_{n−3}) → Ind(P_{n−1}) → Ind(C_n)`.

- `n ≡ 2 (mod 3)`: `Ind(P_{n−1})` is contractible, so `Ind(C_n) ≃ Σ Ind(P_{n−3})`,
  a sphere.
- `n ≡ 1 (mod 3)`: `Ind(P_{n−3})` is contractible, so `Ind(C_n) ≃ Ind(P_{n−1})`,
  a sphere.
- `n = 3k`: `Ind(P_{n−3}) ≃ S^{k−2}` maps into `Ind(P_{n−1}) ≃ S^{k−1}`, and
  every map from a lower-dimensional sphere is null-homotopic. So
  `Ind(C_n) ≃ S^{k−1} ∨ S^{k−1}`. (For `k = 1` this is `C_3`; for `k = 2`,
  `Ind(P_3) ≃ S^0 → Ind(P_5) ≃ S^1` is null because `S^1` is connected.)

Combining the components with tool 1 proves the claim. These are the
classical computations of Kozlov, "Complexes of directed trees", J. Combin.
Theory Ser. A 88 (1999); the argument here is self-contained.
