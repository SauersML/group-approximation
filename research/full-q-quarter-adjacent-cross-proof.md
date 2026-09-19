---
rg: 2
id: full-q-quarter-adjacent-cross-proof
kind: route
title: Compute the native quarter-source cross operator on both adjacent-character orbits
target: full-q-quarter-adjacent-profiles-have-half-cross
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - full-moving-hecke-packet-retains-q-kernel-profile
---

Use the five Levi-coordinate bit order

```text
(u_0,u_1,u_2,u_3,u_4)=(q@5,e_1@7,e_2@8,e_3@9,e_3@2). (1)
```

The two nonzero vector/covector character orbits consist of pairs
`(a,b)` with `a,b in F_2^5-{0}` and

```text
a(b)=epsilon,                    epsilon in {0,1}.      (2)
```

They have respectively `465` and `496` states.  The complete signed source
packet acts exactly as in
`full-moving-hecke-q-kernel-profile-proof`: the ten signed equations cut
out `4` components for `epsilon=0` and `12` components for `epsilon=1`.
The literal roots and adjacent Whiteheads act by

```text
r=x_(u_2,u_0)(1),          l(a,b)=(-1)^(b_3),
J_1=(u_1 u_2),             J_2=(u_2 u_3),              (3)
```

simultaneously on the covector and vector coordinates.

Applying `(1+r)(1+l)` to the signed-component bases gives one orthogonal
basis vector for `epsilon=0` and three for `epsilon=1`.  Up to the common
coefficient `2`, their supports are

```text
epsilon=0:
 {(17,17),(19,17),(21,17),(23,17)},

epsilon=1:
 {(1,1),(3,1),(5,1),(7,1)},
 {(1,17),(3,17),(5,17),(7,17)},
 {(17,1),(19,1),(21,1),(23,1)}.                        (4)
```

The first swap in `(3)` fixes every equal sum in `(4)`.  The second swap
fixes the first two coordinates of each four-point support and carries the
last two to new coordinates.  Explicitly its three pairing-one images are

```text
{(1,1),(3,1),(9,1),(11,1)},
{(1,17),(3,17),(9,17),(11,17)},
{(17,1),(19,1),(25,1),(27,1)},                         (5)
```

and its pairing-zero image is

```text
{(17,17),(19,17),(25,17),(27,17)}.                    (6)
```

Every vector in `(4)` has squared norm `16` with the common coefficient
`2`.  Its corresponding image in `(5)` or `(6)` has exactly two of the
four coordinates in common, so the inner product is `8`.  Different rows
in `(4)--(5)` have disjoint supports.  Therefore, in the displayed
orthogonal bases,

```text
T_1^*T_1=16 I,                 T_1^*T_2=8 I.           (7)
```

Normalizing the source basis proves `T_1^*T_2=(1/2)I_F`.  Squaring and
taking the normalized matrix trace gives `(QAC3)`.

The union of the two range bases has rank `2 rank(F)` in both cases, so
their projection meet is zero.  This is compatible with the nonzero cross
operator because projection meet and Hilbert-space angle are different
invariants.

`experiments/full_q_quarter_native_target_audit.py` repeats the signed
component construction, prints the supports `(4)--(6)`, and verifies the
two exact diagonal matrices in `(7)`.  It was run with Python 3.11 through
the MSI wrapper and completed in under two seconds.
