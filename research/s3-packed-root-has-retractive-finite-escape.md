---
rg: 2
id: s3-packed-root-has-retractive-finite-escape
kind: claim
title: The packed S3 endpoint root has an exact retractive finite escape
artifacts:
  - research/artifacts/s3-packed-root-retraction-audit-2026-08-23.md
distinct_from:
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that proves the six-row Pythagorean packing identity; this proves that its root coordinate can vanish in an exact finite packet while the packed row stays nonzero.
  canonical-root-coordinate-is-binary-not-an-l2-authenticator: that gives the abstract canonical-microstate dichotomy; this supplies a concrete three-convention payload and a nontrivial finite positive-root quotient.
  local-steinberg-heisenberg-packets-are-coefficient-rank-blind: that varies the rank of a retained idempotent root packet; this kills the designated commutator root while retaining both input root lines and the entire S3 endpoint convention table.
---

**ESTABLISHED.**  The three `S3` endpoint conventions admit exact scalar
common-source data with

```text
F_00=F_01=F_11=0,
[Q,Z_X]=[Q,Z_Y]=0,
sum_(b,j)||A_(b,j)V_b-V_bZ_j||_2^2=8.                 (PRE1)
```

For its six-row orthogonal packing `R`, one has exactly

```text
6||R||_2^2=8.                                         (PRE2)
```

At the same time the positive-root Steinberg table over `F_5` has a
25-dimensional permutation model factoring through
`UT_3(F_5)/Z(UT_3(F_5))`.  In this model both input root lines are nontrivial,
all root-additivity and multiplication-triangle relations are exact, but

```text
x_13(c)=1                 for every c in F_5.          (PRE3)
```

The model extends by the standard affine `S3` action on `F_5^2` and by an
independent faithful central `C2` twist.  Neither extension changes `(PRE1)`
or `(PRE3)`.

Consequently, no estimate of the form

```text
sum_(b,j)||D_(b,j)||_2^2
 <=K( ||x_13(R)-1||_2^2
       +sum_b tau(F_b)+sum_j||[Q,Z_j]||_2^2 )          (PRE4)
```

can follow from the endpoint interface, a retractive local root table,
`S3` covariance, and central twists alone: the audited model has right side
zero and left side eight.

More generally, if a root-naming extension retracts to its payload group by
killing the adjoined root subgroup, the scalar payload in `(PRE1)` extends
through that retraction and gives the same countermodel.  Therefore a
successful common-source cell must contain a genuinely mixed,
**non-retractive** relation whose finite-matrix consequence is
one-coordinate kernel reflection from `x_13(R)` to the concrete coefficient
`R`.  Merely adding more root additivity, positive-root triangles, finite
symmetry, or central twists cannot supply that implication.

This claim does not refute such a non-retractive matrix-only relation and
does not assert that the scalar payload extends to the full Fanizza
presentation.  It proves the exact boundary of the packed-root shortcut.

