---
rg: 2
id: automorphism-immersion-representatives-have-finite-order
kind: claim
title: A graph immersion representing a free-group automorphism is a graph automorphism, so its mapping torus is not hyperbolic
distinct_from:
  random-ascending-hnn-of-free-groups-contain-surface-subgroups: that finds surfaces in HNN extensions along endomorphisms; this shows its immersion criterion can never reach hyperbolic free-by-cyclic groups.
---

Let `R` be a finite connected graph with no vertex of valence one, `F = pi_1(R)`,
and let `f: R -> R` be an immersion of graphs (a locally injective simplicial map,
after subdividing the domain) whose induced map on `pi_1`, composed with a change
of basepoint, is an automorphism `phi` of `F`. Then:

1. `f` is a combinatorial automorphism of `R`;
2. the outer class of `phi` has finite order;
3. if `F != 1`, the mapping torus `F *_phi = F x|_phi Z` contains a subgroup of
   finite index isomorphic to `F x Z`. So it contains `Z^2` and is not hyperbolic.

**Consequence for Gromov's question.** If `F x|_phi Z` is hyperbolic, no
representative of `phi` on any finite core graph is an immersion. So
Calegari--Walker's criterion `proposition:f_folded_injective` (which assumes
`f: R -> R` is an immersion; see
`random-ascending-hnn-of-free-groups-contain-surface-subgroups`) never applies to a
hyperbolic free-by-cyclic group. For automorphisms only their bounded-folding
criterion `proposition:bounded_f_folding_injective` is available. Their own remark
(arXiv:1212.2618, l.1311--1320) gets immersion representatives from Reynolds'
theorem only for irreducible endomorphisms that are *not* automorphisms, which is
consistent with this.

Elementary; no novelty claimed. The proof is in
`automorphism-immersion-representatives-finite-order-proof`.
