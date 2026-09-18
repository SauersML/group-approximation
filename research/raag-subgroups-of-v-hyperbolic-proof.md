---
rg: 2
id: raag-subgroups-of-v-hyperbolic-proof
kind: route
title: Proof that RAAGs in V are products of free groups containing no one-ended hyperbolic groups
target: raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group
requires: []
---

Lane proof, elementary.

**Import.** `Z^2 * Z` does not embed in `V` (Bleak--Salazar-Díaz). This is quoted
from BBMZ arXiv:2306.16356v3 Theorem 4.6(1) in `closed-mcg-v-nonembedding-via-koberda`.

**1.** For an induced subgraph `Λ ⊆ Γ`, `A_Λ ≤ A_Γ` (it is a retract). If `Γ` had an
induced subgraph `K_2 ⊔ K_1`, then `Z^2 * Z = A_{K_2 ⊔ K_1} ≤ A_Γ ≤ V`, which is
impossible. The complement of `K_2 ⊔ K_1` is the path `P_3`. So the complement graph
`Γ^c` has no induced `P_3`: whenever `u ~ v` and `v ~ w` in `Γ^c` with `u ≠ w`, also
`u ~ w`. Adjacency-or-equality in `Γ^c` is then an equivalence relation, and `Γ^c` is
a disjoint union of cliques of sizes `n_1, ..., n_k`. So `Γ` is the join of the
edgeless graphs on `n_1, ..., n_k` vertices. A join of graphs gives a direct product
of RAAGs, and an edgeless graph gives a free group. Hence
`A_Γ ≅ F_{n_1} × ... × F_{n_k}`.

**2.** Let `G ≤ F_1 × ... × F_k` be torsion-free, hyperbolic and non-elementary. Let
`N_i` be the kernel of the i-th projection `G → F_i`, so `N_1 ∩ ... ∩ N_k = 1`.

*Lemma.* Two nontrivial normal subgroups `A, B` of `G` intersect nontrivially.
- Take `1 ≠ a ∈ A`. In a torsion-free hyperbolic group the centralizer `C(a)` is
  cyclic.
- If `B ⊆ C(a)`, then `B = ⟨b⟩` is infinite cyclic and normal. Conjugation gives
  `G → Aut(Z) = Z/2`, whose kernel `C(b)` has index `<= 2` and is cyclic. So `G`
  would be virtually cyclic, contrary to non-elementary.
- Hence some `b ∈ B` has `[a,b] ≠ 1`. We have `[a,b] = a·(b a^{-1} b^{-1}) ∈ A` and
  `[a,b] = (a b a^{-1})·b^{-1} ∈ B`.

By induction, a finite intersection of nontrivial normal subgroups of `G` is
nontrivial. So some `N_i = 1`, `G` embeds in `F_i`, and `G` is free (Nielsen--Schreier).

**3.** Suppose a hyperbolic `G` has a finite-index subgroup `K ↪ A_Γ`. Then `K` is
hyperbolic, and torsion-free because `A_Γ` is. If `K` is elementary it is trivial or
cyclic, so `G` is finite or virtually cyclic. Otherwise, by 1 and 2, `K` is free. In
every case `G` is virtually free, hence not one-ended. Closed hyperbolic surface and
3-manifold groups are one-ended. ∎
