---
rg: 2
id: fpbs-product-fibre-bounded-width-branching-fails-proof
kind: route
title: Domination by a critical binomial Galton-Watson tree, the hitting-time theorem and Robbins' Stirling bounds give an n^{-1/2} cluster tail, and Theorem B of the fibre certificate forces chi of order 1/p
target: fpbs-product-fibre-bounded-width-branching-fails
requires:
  - fpbs-fibre-renormalized-nonbacktracking-certificate
---

The complete argument is in section `## Proof` of the target, Steps 1-7. These
are the load-bearing points.

1. **Domination.** For `p <= 1/(D-1)` the exploration of `C` is dominated by a
   Galton--Watson tree, and `|C| <=_st T_1 + T_2`, with `T_i` iid total progeny
   of the critical `Bin(m,1/m)` tree.
2. **Tail.** By the hitting-time theorem (Otter--Dwass; van der Hofstad,
   *Random Graphs and Complex Networks* Vol. 1, Theorem 3.14),
   `P(T=n) = (1/n)P(Bin(nm,1/m) = n-1)`. Robbins' Stirling bounds make this at
   most `0.62 (n-1)^{-3/2}`. Summing gives `P(|C| >= n) <= 12 n^{-1/2}`.
3. **Landing sets.** Integrating the tail gives `E[min(1,p|C|)] <= 24 sqrt(p)`.
   Summing it gives `sum_{n<=K} n P(|C|=n) <= 24 sqrt(K)`.
4. **Imported.** Theorem B of `fpbs-fibre-renormalized-nonbacktracking-certificate`,
   with `N = B` and `d' = d_H`, gives `p(d_H chi - 1) >= 1` for every
   `p ∈ (p_c(G), p_c(B))`. Finiteness of `chi` below `p_c(B)` is sharpness of
   the phase transition on transitive graphs (Menshikov; Aizenman--Barsky).
5. **Width.** Per child fibre, the offspring count is at most
   `M · 1{landing set nonempty}`. Summing over `S_H` gives the bound
   `24 M d_H sqrt(p)`.
