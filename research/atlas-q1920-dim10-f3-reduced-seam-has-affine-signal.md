---
rg: 2
id: atlas-q1920-dim10-f3-reduced-seam-has-affine-signal
kind: claim
title: The ten-dimensional F3 Q1920 packet has an exact affine collision signal before the C144 relation
artifacts:
  - experiments/atlas_a4_q1920_f3_seam_export.g
  - experiments/atlas_a4_q1920_f3_seam_polynomial.sage
  - experiments/atlas_a4_q1920_f3_dim10_affine_witness.sage
  - research/artifacts/atlas-a4-q1920-f3-dim10-affine-seam.json
distinct_from:
  atlas-q1920-six-dimensional-f3-seam-is-signal-free: that excludes both faithful six-dimensional local modules; this supplies a positive exact signal on a ten-dimensional module and identifies the one omitted forward-fan relation.
  atlas-q1920-clifford-four-dimensional-shortcut-fails: that only lists faithful local module dimensions and fixed spaces; this solves the reduced collision equations on one such module.
---

On marking one, irreducible module six, the faithful `Q1920` action on
`E=F3^10` has a nineteen-dimensional algebra `End_A(E)` and a
three-dimensional `A=<r,u>` fixed space.  Write a general `A`-central matrix
as `c=sum x_i e_i` and a general fixed row vector as `v=sum v_j f_j`.
The exact equations

```text
c^2=1, (c t)^3=1, q19243(c,t,s)=1,
v c=-v, v nonzero,
x_i^3=x_i, v_j^3=v_j
```

have the triangular Groebner basis recorded in the JSON artifact.  In
particular `x0=-1`, `x8=1`, all other `x_i=0`, `v0=1`, and `v1=v2=0`
give an explicit solution over `F3`.

Embed the local matrices into homogeneous dimension eleven and let `z` be
translation by `v`.  The verifier checks every relation of `Q1920`, all
`F=<r,z,c,u>` and `J=<t,s,c>` seam relations, and collision `q19243`.
Both protected elements are nonidentity, and exact group orders are

```text
|Q|=1920, |F|=36, |J|=24,
|<Q,c>|=30720,
|<Q,c,z>|=1813985280=3^10*30720.          (Q1920-F3D10-1)
```

This is not a full-packet carrier.  The forward subgroup
`<r,z,b>` has order `324`, not `144`, and the omitted C144 relator
`(z b)^3=1` fails.  Thus collision, the two protected local margins, and the
common `A`-centralizer equations do not annihilate the signal.  Any valid
all-dimensional collapse proof must use the C144 attachment (equivalently
this missing relator), not only the reduced seam operator system.

## Attempts

Imposing only the involution, triangle, collision, and inversion equations
does not kill the ten-dimensional signal: the displayed affine completion is
an exact counterexample.  The next attack is to add `(z b)^3=1`.  It cannot
hold in this homogeneous realization because `z` is a pure translation and
the linear part of `(z b)^3` is the nonidentity involution `b`; a full-packet
argument therefore has to use the nonlinear placement of `z` before passage
to a chief-factor layer.
