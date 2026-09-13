---
rg: 2
id: artin-sigma1-living-subgraph-bounds
kind: claim
title: "Meier's bounds for Sigma^1 of Artin groups: a connected dominant living subgraph gives membership, and membership forces the full living subgraph to be connected and dominant"
distinct_from:
  artin-sigma1-conjecture-known-families: that records complete computations for special graph families; this records two inclusions valid for every Artin group
---

For every Artin group `A_Γ` and every nonzero character `χ : A_Γ -> R`
(notation as in `artin-sigma1-is-connected-dominant-living-subgraph`):

1. if `Liv^χ` is connected and dominant, then `[χ] ∈ Σ^1(A_Γ)`;
2. if `[χ] ∈ Σ^1(A_Γ)`, then `Liv_0^χ` is connected and dominant; in particular
   `Liv^χ` is dominant.

Also, for every Artin group, `Σ^1(A_Γ) = -Σ^1(A_Γ)` (Blasco-García,
Cogolludo-Agustín, Martínez-Pérez, J. Pure Appl. Algebra 226 (2022), Proposition 3.1,
quoted as Lemma 2.8 in arXiv:2501.08692v3). For a discrete `χ` onto `Z` this gives:
`[χ] ∈ Σ^1(A_Γ)` iff `ker χ` is finitely generated (Bieri–Renz, Theorem 2.7 there,
with `n = 1`).

Part 2 accounts for dead vertices and for cuts of `Liv_0^χ`: in both cases `A_Γ`
splits over a special subgroup on which `χ` vanishes. The gap between the two
parts is exactly the dead edges.
