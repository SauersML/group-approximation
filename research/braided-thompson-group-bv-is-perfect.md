---
rg: 2
id: braided-thompson-group-bv-is-perfect
kind: claim
title: The braided Thompson group bV is perfect, so H_1(bV; Z) = 0
distinct_from:
  braided-thompson-group-bv-is-acyclic: that claim asserts vanishing of H_k(bV; Z) in every degree k >= 1; this is only degree one
---

The Brin–Dehornoy braided Thompson group `bV` equals its commutator subgroup,
so `H_1(bV; Z) = 0`. This is the degree-one case of
`braided-thompson-group-bv-is-acyclic`, the affirmative answer to Zaremsky
Problem 2.9 (`zaremsky-2-09-braided-v-acyclic`).

Two independent arguments are in the proof route
`braided-thompson-group-bv-is-perfect-proof`:

1. a self-contained computation, which is load-bearing: the coinvariants of
   `H_1` of the kernel of `bV → V` vanish;
2. a corollary of Zaremsky's theorem that every proper normal subgroup of
   `bV` lies in the kernel of `bV → V` (arXiv:1403.8132).

The degree-one step also records `H_1(K) ≅ C_c(Y, Z)`, where `K` is the
kernel of `bV → V` and `Y` is the space of unordered pairs of distinct points
of the Cantor set. This is the input the degree-two analysis needs.
