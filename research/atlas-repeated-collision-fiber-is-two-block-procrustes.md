---
rg: 2
id: atlas-repeated-collision-fiber-is-two-block-procrustes
kind: claim
title: The repeated regular-S3 collision fiber has an exact two-block Procrustes projection
artifacts:
  - experiments/atlas_a4_common_u_theta_slice.py
  - research/artifacts/atlas-a4-common-u-theta-slice-2026-08-21.json
distinct_from:
  atlas-mixed-c3-gram-has-local-zero-interval: that computes the mixed Gram range after forgetting the conjugator; this optimizes a concrete repeated six-dimensional subfiber of conjugators relative to the fixed packet alignment.
  atlas-common-u-is-twelve-double-coset-system: that retains the full U(10080)^2 involution centralizer and all twelve cyclic-centralizer products; this is the exact projection only on the block-repeated U(3)^2 slice.
---

Write the regular `K~=S3` restriction as

```text
H=directSum_(j=1)^3360 C^6,
B_0=I_3360 tensor b,                                  (RCP1)
```

where `b` is the local right-reflection involution, with eigenspaces of
dimensions three and three.  Let `T_theta=I tensor t_theta`, where `t_theta`
rotates only the trivial/sign lines.  Fix the deterministic involution-pair
conjugator used in the canonical lift, so

```text
U_0=R A^(-1) q,
U_(theta,C)=U_0 (I tensor C) T_theta A,                (RCP2)
```

with `A` the stored collision alignment and

```text
C in U(6), [C,b]=0 ~= U(3) x U(3).                    (RCP3)
```

Every member of `(RCP2)` has exactly the same collision observable:

```text
U_(theta,C)^* rho(b_0) U_(theta,C)
 =A^* T_theta^* B_0 T_theta A.                        (RCP4)
```

In particular collision 19243 remains exact and the positive mixed line
angle is not sacrificed by optimizing `C`.

Put

```text
W_theta=q^(-1) T_theta^*,
M_theta=(1/3360) sum_j (W_theta)_(j,j),                (RCP5)
```

where `(W_theta)_(j,j)` is the diagonal `6 x 6` block in `(RCP1)`.  If
`Q_+` and `Q_-` are isometries onto the two eigenspaces of `b`, then the exact
nearest-reference distance in this repeated collision fiber is

```text
min_([C,b]=0) ||U_(theta,C)-R||_2^2
 =2-(1/3)( ||Q_+^*M_theta Q_+||_*
           +||Q_-^*M_theta Q_-||_* ).                 (RCP6)
```

Thus the nominal `20160`-dimensional projection is exactly two `3 x 3` polar
decompositions.  The minimizing blocks are the polar factors of the two
compressions in `(RCP6)`.

This is only the block-repeated subfiber.  The full centralizer of one regular
involution is `U(10080) x U(10080)` and can mix the `3360` copies.  Nor does
distance from the single alignment `R` lower-bound distance from all twelve
shifted centralizer products.  Consequently `(RCP6)` is a finite exact
coordinate reduction and a search fence, not a proof of the common-`U`
compiler.

The bounded MSI run found no promising point.  With twelve fixed Hutchinson
probes, the Procrustes minimizers at `theta=0,0.1,0.4,pi/4` had packet RMS
defects `1.3906,1.3912,1.3972,1.4044`; their exact Procrustes distance-squared
values to `R` were approximately `1.4291,1.4289,1.4335,1.4523`.  These
numbers are signal about this one subfiber only.

The restriction to this subfiber cannot be removed by averaging.
`atlas-collision-fiber-has-no-block-symmetrization` proves
that the `K`-copy group is not a packet symmetry, the packet energy is
nonconvex, and even the genuine scalar symmetry has zero Haar barycenter on
every collision fiber.  A global promotion would need a new nonzero-overlap
or direct twelve-product argument.
