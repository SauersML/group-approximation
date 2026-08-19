---
rg: 2
id: commuting-involution-mass-is-four-times-rank
kind: claim
title: For commuting involutions the Frobenius mass is exactly four times a projection rank
distinct_from:
  involutive-compression-collapse: that is the analytic collapse theorem for the involutive lamp class; this is the metric calculus it is calibrated against, and it is a statement about two matrices with no group, compression or corona in it.
  corona-commuting-torsion-lifts: that asks for exact commuting lifts of approximately commuting torsion unitaries; this compares three metrics on a pair of exact involutions that are already given.
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - GroupApproximation/Sofic/InvolutionRankMass.lean
---

Call a self-adjoint matrix squaring to `1` an **exact involution**.  For two
commuting exact involutions `u`, `w` the displacement `T = u - w` is
self-adjoint and satisfies `T^3 = 4T`, so `T^2/4` is an orthogonal projection —
the **half-square projection** of the pair — and

    ‖u - w‖_F^2 = 4 . rank (T^2/4).

So on this locus the unnormalized Frobenius mass and the rank are the *same*
invariant, with no inequality lost.  Three further comparisons make the rank
displacement a usable metric and give the reverse bound in general:

- `rank(a - c) <= rank(a - b) + rank(b - c)`: matrix rank obeys the triangle
  inequality along differences;
- orthogonal projections at operator distance strictly less than `1` have
  **equal** rank;
- for an arbitrary square matrix, `‖X‖_F^2 <= rank X . ‖X‖_op^2`.

## Why the exact factor matters

The scaled transport theory measures matrices by unnormalized Frobenius mass and
is calibrated against an arbitrary weight sequence.  The weight of interest in
the analytic collapse argument is a *rank* scale, so mass and rank have to be
compared exactly and not merely up to a dimension factor — a dimension factor is
precisely what a normalization argument cannot afford.  The identity above is
what turns a mass-calibrated transport statement into a rank-calibrated one, and
`4` is the whole conversion.

The conceptual separation of the three metrics that this claim relates — operator
norm for the algebraic and covariance control, rank for the discrete support that
survives normalization, Hilbert--Schmidt for the energy that property (T) acts on
— was prompted by a question of Francesco Fournier-Facio.

The projection-rigidity clause is the piece that does real work downstream: it is
what converts an *approximate* statement about projections into an *exact*
statement about ranks, which is how a rank invariant survives passage to a limit
at all.
