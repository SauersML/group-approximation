---
rg: 2
id: matricial-mautner-fixed-subspace
kind: claim
title: A compressed conjugate has the same Kazhdan projection in a matrix corona
distinct_from:
  scaled-kazhdan-transport: That claim is a weighted asymptotic-commutant transport at the finite stages, quantified over every nonnegative weight and stated for mass-bounded Frobenius sectors; this one is the exact equality of two projections inside the corona itself, with stable finiteness as the whole proof and no scale, weight, or almost-representation in the statement.
  kazhdan-asymptotic-commutant-transport: That is a dimension-normalized transport statement about commutants of an almost representation; this is a projection identity in the corona C*-algebra.
  corona-projection-collapse: That takes an arbitrary corona projection with two orbit hypotheses (centralized by the compressed copy, commuting conjugation orbit) and concludes it commutes with the whole Kazhdan image, by way of the involutive collapse theorem; this concerns the two canonical Kazhdan projections only, assumes no orbit condition, and is proved in three lines from stable finiteness with no analytic input at all.
artifacts:
  - research/artifacts/collapse-criterion-source-2026-08-16.md
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

Let `Q` be a norm matrix corona, `Gamma` a countable Kazhdan group, and
`pi : Gamma -> U(Q)` any homomorphism extending to `C*max(Gamma) -> Q`.  Let
`t` be a unitary of `Q` with

    H := t pi(Gamma) t^-1  <=  pi(Gamma).

Write `p_Gamma` and `p_H` for the images of the two Kazhdan projections.
Then

    p_H = p_Gamma.

Equivalently: an element of the corona fixed by the compressed conjugate copy
is already fixed by the whole Kazhdan group.  This is the exact-projection
form of the reversal step; nothing about ranks, scales, or stages enters the
statement.
