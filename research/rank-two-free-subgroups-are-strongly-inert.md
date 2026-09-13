---
rg: 2
id: rank-two-free-subgroups-are-strongly-inert
kind: claim
title: Subgroups of rank at most two of a free group are strongly inert
distinct_from:
  linton-z-stable-one-relator-hierarchy-theorem: that is Linton's hierarchy criterion, whose inertial one-relator extensions need strongly inert edge groups; this is the free-group input that supplies the hypothesis for rank-two edge groups.
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
---

**Import.** Let `F` be a free group and `H <= F` a subgroup of rank at most 2. Then for
every subgroup `K <= F`,

    sum over double cosets K g H of  rr(H cap K^g)  <=  rr(K),

where `rr(A) = max{0, rk(A) - 1}`. So `H` is strongly inert in the sense of Linton
(*One-relator hierarchies*, arXiv:2202.11324v3, p. 5: "A subgroup `H < G` is ... strongly
inert if for every subgroup `K < G`, we have `sum_(KgH) rr(H cap K^g) <= rr(K)`").

**Source statements (J. Friedman, *Sheaves on graphs, their homological invariants, and a
proof of the Hanna Neumann conjecture*, arXiv:1105.0129v2, 17 Jun 2011).**
- p. 60, (2.4): the Strengthened Hanna Neumann Conjecture is
  `sigma(K, L) <= rk_(-1)(K) rk_(-1)(L)`, where
  `sigma(K, L) = sum over K x F in K\F/L of rk_(-1)(K cap x^(-1) L x)` and
  `rk_n(G) = max(rank(G) + n, 0)`.
- p. 60, item (1): "K is universal for the SHNC if it is of rank at most three ([DF01]), in
  view of equation (2.5), with rank two settled earlier by Tardos ([Tar92])".
- p. 62, Theorem 2.2: "The Strengthened Hanna Neumann Conjecture holds."

**Why this gives the claim.** `rk_(-1) = rr`. If `rank H <= 2` then `rr(H) <= 1`, so (2.4)
with the pair `(H, K)` gives `sum_g rr(H cap K^g) <= rr(K)` for finitely generated `K`. When
`K` is not finitely generated, `rr(K)` is infinite and the inequality is trivial. Friedman
reduces the SHNC to `F = F_2` (p. 60: "any finitely generated free group, F, is a subgroup of
F_2"). The double-coset sum over the ambient `F` is the same sum, since intersections are
computed inside `F`.
