---
rg: 2
id: higman-approximate-torsion-collapses-hs-word-ratio
kind: claim
title: Approximate torsion of any single Higman generator forces a dimension-free linear word bound
distinct_from:
  higman-order-three-torsion-ratio-bound: that gives the explicit constant 25397 when both odd generators are near order three; this covers any fixed exponent on any one generator, with a non-explicit (tower-type) constant.
  hyperlinear-radical-has-linear-word-certificate: that is the unrestricted certificate equivalent to radical membership; this proves the certificate after adding one torsion energy term, which says nothing about the radical by itself.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that reduces microstates to glued BS packets; this is Higman's smallest-prime argument made quantitative in the normalized HS norm.
artifacts:
  - research/artifacts/higman-hs-ratio-scaling-scout-2026-09-17.md
  - experiments/higman-hs-microstate-scaling-2026-09-17/check_torsion_bound.py
---

Let `Hig=<g_0,...,g_3 | g_j g_(j+1) g_j^(-1)=g_(j+1)^2, j in Z/4>` and
`r_j=g_j g_(j+1) g_j^(-1) g_(j+1)^(-2)`. For every integer `m>=1` and every
`i in Z/4` there is a finite constant `K_(m,i)` with the following property.
For unitaries `g_0,...,g_3` in any tracial von Neumann algebra, in
particular in `U(d)` for every `d`,

```text
e(g_0) <= K_(m,i) ( sum_j e(r_j) + e(g_i^m) ),      e(v)=||v-1||_2^2 .
```

What it rules out. If a sequence of tuples has
`e(g_0)/sum_j e(r_j) -> infinity`, then for every generator `g_i` and every
fixed exponent `m`, `e(g_i^m)/sum_j e(r_j) -> infinity`. That sequence is
exactly what `C(4)=infinity`, i.e. hyperlinearity of Hig, would require.
So every generator must avoid all fixed finite orders at a scale far above
the defect. Every fixed-order torsion ansatz on any single generator (exact
spectrum in the `m`-th roots of unity) is therefore capped by a
dimension-free constant. This covers the order-q runs for every fixed q.
Only spectra whose torsion exponent grows with the sequence (for example
all d-th roots in dimension d) remain. The order-three case, with an
explicit constant, is `higman-order-three-torsion-ratio-bound`.
