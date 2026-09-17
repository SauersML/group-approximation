---
rg: 2
id: fpbs-hermon-hutchcroft-supercritical-analyticity
kind: claim
title: Truncated finite-cluster observables of Bernoulli percolation are analytic throughout the supercritical phase on nonamenable transitive graphs
distinct_from:
  fpbs-supercritical-finite-susceptibility: that records finiteness of the truncated susceptibility at each fixed p>p_c; this records analyticity (hence continuity and local boundedness on compact subintervals of (p_c,1)) of such observables as functions of p
---

**Published input.** Let `G` be a connected, locally finite, nonamenable,
transitive graph, `v` a vertex, and `F` a function on finite connected
subgraphs containing `v` with subexponential growth. Then
`p -> E_p[F(K_v) 1(|K_v| < infinity)]` is analytic on `(0,p_c) ∪ (p_c,1)`.

Taking `F(H) = |V(H)|` (which is at most `|E(H)|+1`, so of subexponential
growth) gives that the truncated susceptibility
`chi^f(p) = E_p[|K_v|; |K_v| < infinity]` is analytic, hence continuous, on
`(p_c,1)`. In particular `sup_{s in [a,b]} chi^f(s) < infinity` for every
compact `[a,b] ⊂ (p_c,1)`. That local boundedness is the only consequence used
downstream (`fpbs-sharp-dominating-collapse-over-sparse-spines`).

Imported by `fpbs-hermon-hutchcroft-analyticity-citation`.
