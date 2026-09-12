---
rg: 2
id: full-q-native-quarter-source-has-distinct-literal-ranges
kind: claim
title: The full-Q native quarter source need not have one literal Whitehead range
artifacts:
  - research/full-q-native-quarter-range-counterprofile-proof.md
  - experiments/full_q_native_quarter_range_audit.py
distinct_from:
  b2-b3-pair-full-hecke-four-native-sectors: that proves a representation-universal rank-one-quarter common source for the two native compressions; this shows that the two literal Whitehead images of that source need not be the same projection.
  full-moving-hecke-packet-retains-q-kernel-profile: that makes the endpoint compression QWQ vanish on the same 465-state constituent; this computes the distinct J1F and J2F ranges and retains a positive cross coefficient between them.
  same-center-whitehead-native-selector-subcorner-attachment: that permits a model-dependent polar target with controlled mass and label covariance; this refutes only the shortcut which declares the two literal range projections equal.
---

**ESTABLISHED COMMON-RANGE FENCE.**  Retain the full Hecke source and its
joint native sign cut

```text
F=Q(1+r)(1+l)/4,       r=x_58(a_2),       l=x_69(a_3) (FQR1)
```

from `b2-b3-pair-full-hecke-four-native-sectors`.  Since `F` lies in both
native compression supports, the two literal partial transports out of
this source are

```text
T_1=J_1F,                   T_2=J_2F,                 (FQR2)
R_1=T_1T_1^*=J_1FJ_1,       R_2=T_2T_2^*=J_2FJ_2.   (FQR3)
```

Both `R_i` lie under the common ambient projection `p_2`.  They need not be
the same range projection, however.  In the exact `465`-state parabolic
constituent of `full-moving-hecke-packet-retains-q-kernel-profile`, one has

```text
rank(F)=1,             R_1!=R_2,             R_1 meet R_2=0. (FQR4)
```

More explicitly, in its monomial basis indexed by row/vector pairs, a
nonzero vector spanning `F` is

```text
f=e_(17,17)+e_(19,17)+e_(21,17)+e_(23,17).           (FQR5)
```

The literal adjacent swaps act by

```text
J_1f=f,
J_2f=e_(17,17)+e_(19,17)+e_(25,17)+e_(27,17).        (FQR6)
```

The two vectors are noncollinear, proving `(FQR4)`.  Their normalized inner
product is nevertheless

```text
<J_1f,J_2f>/(||f|| ||J_2f||)=1/2.                    (FQR7)
```

Thus this counterprofile does **not** refute positive cross-Gram mass or a
model-dependent polar alignment: its squared scalar Gram is `1/4`.  It
refutes only the stronger inference

```text
common source F  ==>  J_1FJ_1=J_2FJ_2.               (FQR8)
```

The Whitehead star braid also does not repair `(FQR8)` by restriction.
Its reservoir-gauge conclusion applies on a carrier reducing the three
Whitehead actors, whereas `(FQR6)` has `J_2F!=F`; compressing the braid to
`F` has a genuine boundary term.  Likewise the mixed Hecke words
`u_1=B_2A_1` and `u_2=B_3A_2A_1` carry the full source `Q` onto their exact
common range `P`, but after restricting to `F` they give only the two
subprojections `u_iFu_i^(-1)<=P`.  Identifying those Hecke subranges with
the literal native ranges in `(FQR3)` is the occurrence seam, not a
consequence of the common ambient target.

No Property `(T)`, canonical-trace substitution, local computation, or
literature theorem is used.  The finite calculation is audited only through
the MSI wrapper.

DERIVATION
full-q-native-quarter-range-counterprofile-proof
