---
rg: 2
id: euler-characteristic-empties-top-bnsr-invariant
kind: claim
title: "A group with a finite d-dimensional classifying space and nonzero Euler characteristic has empty Sigma^d"
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-top-range-2026-09-13.md
---

Let `X` be a finite connected CW complex of dimension `d` with Euler
characteristic `chi(X) != 0`. Then the homological BNSR invariant
`Sigma^d(X, Z)` is empty. In particular, if `G` has a finite `K(G,1)` of
dimension `d` and `chi(G) != 0`, then `Sigma^d(G; Z) = ∅` and the homotopical
invariant `Sigma^d(G)` is empty.

Model tests: free groups `F_k` (`k >= 2`, `d = 1`, `chi = 1 - k`) and closed
surface groups of genus `>= 2` have empty `Sigma^1`, as they must; `F_2 x Z`
has `chi = 0` and nonempty `Sigma^2`, so the hypothesis `chi != 0` cannot be
dropped.
