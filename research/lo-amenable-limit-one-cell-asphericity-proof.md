---
rg: 2
id: lo-amenable-limit-one-cell-asphericity-proof
kind: route
title: The first Betti number of a one-cell complement is one, so Osin--Thom's bound gives zero
target: lo-amenable-limit-one-cell-complements-are-aspherical
requires:
  - contractible-complex-minus-cell-has-cyclic-homology
  - osin-thom-lo-amenable-limits-satisfy-b1-bound
  - finite-2-complex-with-zero-second-l2-betti-is-aspherical
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

1. `contractible-complex-minus-cell-has-cyclic-homology` gives `H₁(G; Z) = H₁(K; Z) ≅ Z`, `χ(K) = 0`,
   and `G` infinite. `K` is a finite complex, so `G` is finitely generated. The first Betti number is
   `β₁(G) = 1` under any of the usual conventions: the rank of `G^ab`, or `dim H₁(G; Q)`, or
   `dim H₁(G; C)`.
2. `osin-thom-lo-amenable-limits-satisfy-b1-bound` gives `b₁^(2)(G) ≤ β₁(G) − 1 = 0`. L²-Betti
   numbers are nonnegative, so `b₁^(2)(G) = 0`.
3. `G` is infinite and `χ(K) + b₁^(2)(G) = 0`, so
   `finite-2-complex-with-zero-second-l2-betti-is-aspherical` makes `K` aspherical.
