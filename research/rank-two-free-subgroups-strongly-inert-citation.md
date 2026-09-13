---
rg: 2
id: rank-two-free-subgroups-strongly-inert-citation
kind: route
title: Friedman's proof of the Strengthened Hanna Neumann Conjecture specialised to rank-two subgroups
target: rank-two-free-subgroups-are-strongly-inert
requires: []
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
---

**Citation.** J. Friedman, *Sheaves on graphs, their homological invariants, and a proof of the
Hanna Neumann conjecture*, arXiv:1105.0129v2 (17 June 2011); Mem. Amer. Math. Soc. 233 (2015),
no. 1100. Independently, I. Mineyev, *Submultiplicativity and the Hanna Neumann conjecture*,
Ann. of Math. 175 (2012).

**Check.** The statements were read from the arXiv v2 PDF on 2026-09-13: equation (2.4) and
item (1) on p. 60, and Theorem 2.2 on p. 62. Mineyev's paper was not re-read.

**Specialisation.** For `H` of rank at most 2, `rk_(-1)(H) <= 1`, so (2.4) reads
`sum_(x in H\F/K) rr(H cap x^(-1) K x) <= rr(K)`. The double cosets `H x K` and `K x^(-1) H`
correspond, and `H cap x^(-1) K x` is `H cap K^g` with `g = x`. This is Linton's inequality.
The rank-two case also appears in Friedman's text as settled earlier by Tardos (1992), cited
only through Friedman.
