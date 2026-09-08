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

**Independently corroborated, at a worse rank (2026-09-08).**  A forwarded
dossier derived this criterion from scratch under the same hypotheses -- `R`
countable unital, `ts = 1`, `Q = 1 - st` of finite additive order, no fullness
assumption -- and reached `E_n(R, RQR) <= Rad_MF(EL_n(R))` for `n >= 6`, by
building a dilation `v = [[s,Q],[0,t]]` with an explicit elementary
factorisation, a unit `r = (1+sQ)(1-Qt)(1+sQ)` making the compressor
`u = UP` normalise `EL_3` in six coordinates, and then applying
`normal-kazhdan-defect-non-mf` to a finite central `<x_56(Q)>` inside the
subgroup it generates.  Its analytic input is the same, Ershov--Jaikin-Zapirain
Theorem 1.1 for property (T) of the elementary group over a finitely generated
subring.  So the statement above has a second derivation by a different
compressor; the rank there is `6` and the rank here is `4`, so nothing is
gained by adopting it and a reader comparing the two should take `n >= 4`.

The dossier also drew out the instance `R = J = F_2<s,t | ts = 1>` at `n >= 6`,
which is `binary-jacobson-steinberg-head-root-is-mf-invisible`, proved here at
rank five.  Its one genuinely additive observation is the criterion-level
dichotomy recorded on
`kazhdan-criterion-is-inert-on-finitary-permutation-extensions` and
`finitary-linear-extension-kazhdan-defect-kills-kernel`, with the ingestion
record in
`research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md`.
