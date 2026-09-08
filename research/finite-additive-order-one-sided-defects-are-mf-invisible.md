---
rg: 2
id: finite-additive-order-one-sided-defects-are-mf-invisible
kind: claim
root: true
title: Every one-sided inverse defect of finite additive order is MF-invisible in elementary rank at least four
distinct_from:
  locally-finite-defect-subgroup-dies-in-every-corona: that asks for arbitrary locally finite normal subgroups; this settles all finite-additive-order ring defects through a special finitary elementary subgroup with a uniform rank bound.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that is the binary Jacobson group in rank five; this covers arbitrary coefficient rings and every finite additive order in rank four.
artifacts:
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
  - research/artifacts/composite-jacobson-uniform-rank-and-normality-2026-09-08.md
  - research/artifacts/finite-order-one-sided-defect-mf-collapse-2026-09-08.md
---

Let R be a countable unital ring, s,t in R satisfy ts=1, and let
Q=1-st have finite additive order. For every n>=4 and i!=j,

    e_ij(Q) belongs to Rad_MF(E_n(R)).

If Q!=0, E_n(R) is not MF. No assumption RQR=R is needed. In
particular, for rings of positive characteristic, MF of E_4(R)
implies direct finiteness of R.

The proof uses property (T) on an elementary subgroup over a
finitely generated universal ring. It is not a property-(T)-free
proof and carries no new Lean verification claim.
