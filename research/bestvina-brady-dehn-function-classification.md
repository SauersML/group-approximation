---
rg: 2
id: bestvina-brady-dehn-function-classification
kind: claim
title: Finitely presented Bestvina–Brady groups have Dehn function n^d with d in {1,2,3,4} determined by the defining graph
distinct_from:
  stallings-bieri-groups-have-quadratic-dehn-function: that claim is the Carter–Forester theorem for kernels of products of free groups; this is the classification for all finitely presented Bestvina–Brady groups
---

Chang, García-Mejía and Migliorini, *Complete classification of the Dehn
functions of Bestvina–Brady groups*, arXiv:2507.07566 (v1 2025-07-10, v2
2025-12-30), Geom. Funct. Anal. 36 (2026).

Let `Γ` be a finite simplicial graph whose flag complex `Δ(Γ)` is simply
connected (property (D1)). All subgraphs are induced. A graph is reducible if
it is a join of two nonempty subgraphs, and irreducible otherwise. It is
essentially 2-reducible if it is a join of two irreducible subgraphs, each with
at least two vertices. `Γ` has property

- (D2) if `Γ` is not a tree;
- (D3) if `Γ` contains a maximal reducible subgraph that is essentially 2-reducible;
- (D4) if `Γ` contains a maximal reducible subgraph whose flag complex is not simply connected.

Let `d(Γ)` be the largest `α ∈ {1,2,3,4}` such that `Γ` has (Dα). Then
`δ_{BB_Γ}(n) ≃ n^{d(Γ)}` (Theorem 1). Corollary 1: if `Γ` is essentially
2-reducible and `Δ(Γ)` is simply connected, then `BB_Γ` has cubic Dehn
function.

Earlier bounds: Dison (arXiv:0705.4220) proved `δ_{BB_Γ} ≼ n^4` for every
finitely presented `BB_Γ`, and Brady gave cubic and quartic examples (Figure 1
of the paper).
