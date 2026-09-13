---
rg: 2
id: derived-full-group-h2-filtered-by-mod-two-groupoid-homology
kind: claim
title: The second homology of a derived full group is filtered by H_2(G), H_1(G; Z/2) and H_0(G; Z/2), so infinite mod-2 groupoid homology forbids finite presentation
distinct_from:
  li-derived-full-group-homology-is-k-theory-cover: That is Li's identification of the homology of D(G) with that of an infinite loop space; this extracts from it an explicit filtration of H_2(D(G)) and the resulting finite-presentation obstruction and finiteness criterion, which Li does not state.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `G` is an ample groupoid whose unit space is locally compact Hausdorff without isolated points.
- `G` is minimal and has comparison.
- `D(G)` is the commutator subgroup of the topological full group, and `K = K(B_G)` is Li's
  spectrum.

**Theorem 1.** `H_2(D(G); Z) ≅ π_2(K)`, and `π_2(K)` has a filtration
`0 ⊆ F_0 ⊆ F_1 ⊆ F_2 = π_2(K)` with:
- `F_0 ≅ H_0(G; Z/2) / ( d^2 H_2(G; Z/2) + d^3 E^3_{3,0} )`, where `E^3_{3,0} ⊆ H_3(G; Z)`;
- `F_1/F_0 ≅ H_1(G; Z/2) / d^2 H_3(G; Z)`;
- `F_2/F_1 ≅ ker( d^2 : H_2(G; Z) -> H_0(G; Z/2) )`.

**Corollary 2.**
- **(a) Obstruction.** Suppose `H_3(G; Z)` is finitely generated and `H_2(G; Z/2)` is finite.
  If `H_0(G; Z/2)` or `H_1(G; Z/2)` is infinite, then `H_2(D(G); Z)` is not finitely generated,
  so `D(G)` is not finitely presented.
- **(b) Degree 2.** If `H_2(G; Z)`, `H_1(G; Z/2)` and `H_0(G; Z/2)` are finitely generated, then
  `H_2(D(G); Z)` is finitely generated.
- **(c) All degrees.** If `H_p(G; Z)` is finitely generated for all `p <= k`, then
  `H_j(D(G); Z)` is finitely generated for all `j <= k`.

**Model tests.**
- **Thompson's `V`.** `H_*(G_2) = 0`, so `π_2 K = 0`, which matches `H_2(V) = 0`.
- **Cantor minimal `Z`-systems.** Here `H_2(D(G))` is an extension of `Z/2` by
  `K^0(X) ⊗ Z/2`.
  - For Sturmian systems it has order 8, while Matui (math/0404117) shows `D(G)` is never
    finitely presented. So (b) is only a necessary condition and cannot be reversed.
  - Minimal subshifts with `K^0 ⊗ Z/2` infinite get a second, homological, proof.

**Novelty.** None claimed. Li does not state these consequences, and no literature search beyond
Li's source was possible.

Proof: `derived-full-group-h2-filtration-proof`.
