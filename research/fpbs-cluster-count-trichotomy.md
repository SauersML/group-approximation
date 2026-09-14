---
rg: 2
id: fpbs-cluster-count-trichotomy
kind: claim
title: The number of infinite clusters is zero, one or infinity, and one for all p above p_u
---

**ESTABLISHED (imported).** Let `G` be a connected, locally finite,
quasi-transitive graph. Then:

1. **Trichotomy (Newman--Schulman).** For each `p in (0,1)` there is
   `N_infinity(p) in {0, 1, +infinity}` such that the number of infinite
   clusters of Bernoulli bond percolation is a.s. `N_infinity(p)`.
2. **Simultaneous uniqueness (Haggstrom--Peres, Schonmann).** For every
   `p > p_u` the percolation has a unique infinite cluster a.s.,
   `N_infinity(p) = 1`.

Consequently `N_infinity(p) = 0` for `p < p_c`, `N_infinity(p) = +infinity` for
`p_c < p < p_u`, and `N_infinity(p) = 1` for `p > p_u`.

Read from Choi--Seo arXiv:2508.08932v2, Section 2 (page 3), from source
2026-09-11: "[NS81] ... `N_infinity(p) in {0, 1, +infinity}`" and, for
`p > p_u`, uniqueness "due to O. Haggstrom and Y. Peres [HP99] for unimodular
cases, and due to R. H. Schonmann [Sch99] in general".

Status records imported theorems, not independent mathematical verification.

DERIVATION
fpbs-cluster-count-trichotomy-cite
