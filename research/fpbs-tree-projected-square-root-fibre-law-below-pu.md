---
rg: 2
id: fpbs-tree-projected-square-root-fibre-law-below-pu
kind: claim
title: Below p_u on tree-projected Cayley graphs over an amenable normal kernel the cluster hits fibres with square-summable probabilities to every power above two
distinct_from:
  fpbs-tree-projected-pu-l2-iff-square-root-law: that proves this law is equivalent to p_{2->2} = p_u on the same graphs; this is the open assertion that the law holds.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that asks for p_c < p_u; this asks for no gap at all, only a non-strict exponent bound below p_u, and neither implies the other.
artifacts:
  - research/artifacts/fpbs-fibre-power-improvement-2026-09-17.md
---

**OPEN.** Let `N` be an infinite amenable normal subgroup of `Gamma` with
`Q = Gamma/N` free of rank `n >= 2`. Let `S` be finite symmetric with `pi(S)` inside
a basis, its inverses and `1`, and let `G = Cay(Gamma,S)`. Then for every
`p < p_u(G)` and every `r > 2`,

```text
sum_(q in Q) P_p(o <-> Gamma_q)^r < infinity.
```

By `fpbs-tree-projected-pu-l2-iff-square-root-law` this is equivalent to
`p_{2->2}(G) = p_u(G)`. It can fail independently of `p_c < p_u`: a graph could
have a gap and still `p_{2->2} < p_u`. The statement is known for product
generating sets of `F_n x H` (Cayley graph `T x H`). There Hutchcroft--Pan
arXiv:2412.15895 prove `p_{2->2} = p_u`, using the nonunimodular end-fixing symmetry. The smallest open case is `S_rig` in
`F_2 x Z` (`fpbs-tree-projected-rigid-decorations-strict-thresholds`).

Interpretation: below `p_u`, on the sphere of radius `R` in `Q`, the cluster hits
at most "square-root many" fibres in the `l^(2+)` sense. This is
Hutchcroft--Pan's `beta* >= 1/2`, summed over fibres.

## Attempts

* **Backscattering with central translates (2026-09-17, artifact §5).**
  * **What works.** For central `N`, the translate of `{o -> y}` by `g` is
    `{g -> yg}`, so pairs keep their separation exactly. Sprinkling along
    infinitely many common fibres merges the two clusters, which gives
    `inf_g tau(o,g) > 0` and so `p >= p_u`.
  * **Where it stops.** Children must sit in disjoint slabs, so there is at most one
    child per fibre. FKG then bounds the mean below only by
    `sum_q max_h a(g_q h)^2`, not by `sum_q P(A_q)^2`: the height spread of
    `K_o ∩ Gamma_q` is lost. On rigid decorations the height separation is a
    correlated difference, not a symmetric walk, so Kesten's return bound has no
    input.
  * **Second moment.** Counting coincident fibres involves same-fibre sibling
    lineages, which grow at the rate of `b_R` itself.
  * **Missing input: a flat pair lemma.** Exponential growth of
    `sum_(|q|=R) P(A_q)^2` should force exponential growth of
    `sum_(|q|=R) P(exists h : o -> g_q h, g -> g_q h g)`, uniformly in `g`.
