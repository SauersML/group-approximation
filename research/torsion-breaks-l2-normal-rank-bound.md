---
rg: 2
id: torsion-breaks-l2-normal-rank-bound
kind: claim
title: Torsion destroys the first l2-Betti normal-rank bound
invalidates: [simple-kl-via-l2-betti-normal-rank]
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

There is no inequality in the presence of torsion that bounds the first
`l2`-Betti number of a group by its normal rank in the way needed for the
Kervaire--Laudenbach core.

Osin--Thom prove that for every `n>=2` and every `epsilon>0` there is a simple
group `P` with torsion such that

    beta_1^(2)(P) >= n-1-epsilon.

Every nontrivial element of a simple group normally generates it, so each of
these groups has normal rank one while its first `l2`-Betti number can be
arbitrarily large.  Their proposed inequality
`beta_1^(2)(G) <= normal-rank(G)-1` is explicitly a torsion-free conjecture,
not a tool available for the arbitrary simple groups in the Cairn reduction.
