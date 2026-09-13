---
rg: 2
id: graph-braid-ascending-matching-complexes-give-sigma
kind: claim
title: "A generic hyperplane-affine character of B_n Gamma lies in Sigma^m when every ascending move graph has (m-1)-connected matching complex"
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
---

Let `Γ` be sufficiently subdivided, and let `c` be a real function on
oriented hyperplane classes of Abrams' cube complex `UD_nΓ`, antisymmetric
under reversing the edge and nonzero on every class. Then `c` is a 1-cocycle
and defines a character `χ_c` of `B_nΓ`. At a configuration `S` (a set of
`n` vertices), the ascending move graph `B↑_c(S)` is the bipartite graph
between `S` and `V(Γ) \ S` with an edge for each move `v → w` along an edge
of `Γ` on which `c > 0`.

If, for every `S`, the matching complex of `B↑_c(S)` is `(m−1)`-connected
(for `m = 1`: nonempty and connected), then `[χ_c] ∈ Σ^m(B_nΓ)`.

The vertex links of `UD_nΓ` are matching complexes of the full move graphs,
so the ascending links of `h_c` are these matching complexes. The
Bestvina–Brady Morse lemma and the geometric criterion for `Σ^m`
(Bieri–Geoghegan; Bux–Gonzalez 1999; Witzel–Zaremsky arXiv:1501.06682 §1)
give the conclusion. See artifact part 2, §2. Calibration: for `n = 1` it
gives `Σ¹` only for the cycle, consistent with `Σ¹(F_r) = ∅`, `r ≥ 2`.
