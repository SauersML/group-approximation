---
rg: 2
id: atlas-19243-common-u-regular-local-hub-gram-escape
kind: claim
title: Collision 19243 has a common-U continuous hub-Gram escape on the regular S3-by-S3 local cell
distinct_from:
  atlas-19243-has-continuous-regular-s3-line-holonomy: that constructs a balanced collision involution with regular K margin; this retains the literal regular representation of the full local group K by L, fixes the actual collision involution b, constructs one common conjugating U, and computes the hub Gram moments exactly.
  atlas-common-u-second-moment-is-one-projection-gram: that identifies the general projection-Gram coordinate; this gives an exact collision-zero family on which that coordinate varies.
  atlas-a4-collision-assisted-opaque-star-compiler: that additionally imposes the cross-component A4 packet; this proves those packet constraints are indispensable and does not provide a counterexample to their joint conclusion.
---

Let

```text
K=<r,s> ~=S3,       L=<z,b> ~=S3,
[K,L]=1,
```

be the local cell of `atlas-a4-19243-s3xs3-localization`, and work on
`Reg(K x L)`.  There is a continuous family of unitaries `U_theta` such that,
with

```text
c_theta=U_theta b U_theta^*,
q_theta=r c_theta s c_theta r^-1 c_theta (sr)c_theta,
V_theta=c_theta b,
```

one has

```text
q_theta=1,                                                (A4-LOC-Q)

Re tau(V_theta)=(2+cos(2 theta))/3,
tau(V_theta^2)=(2+cos(4 theta))/3,                       (A4-LOC-GRAM)

||V_theta-1||_2^2=(4/3)sin(theta)^2.                    (A4-LOC-HUB)
```

All traces are normalized on the thirty-six-dimensional regular local cell.
The same construction amplifies to `Reg(A8)`, because

```text
Reg(A8)|_(K x L)=560 Reg(K x L).
```

Thus collision defect zero, exact regular local margins, the literal fixed
involution `b`, and a single common relative unitary do not control even the
hub's first or second spectral moment.  In particular there is no inequality

```text
|tau(V_b^2)-1| <= C ||q_19243-1||_2
```

under those hypotheses, for any finite `C`.

This is not a counterexample to the full collision-assisted opaque-star
compiler: `U_theta` is not asserted to satisfy the `H_6` packet component or
all fourteen/thirty shifted common-`U` factorizations.  It proves sharply that
the missing mixed moment must couple the collision line carrier to the other
packet component.  No identity internal to the full regular `S3 x S3` local
cell can supply it.
