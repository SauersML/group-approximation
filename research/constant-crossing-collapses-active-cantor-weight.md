---
rg: 2
id: constant-crossing-collapses-active-cantor-weight
kind: claim
title: One constant crossing plus the native depth mismatch collapses every active Cantor weight
artifacts:
  - research/constant-crossing-cantor-weight-proof.md
distinct_from:
  endpoint-native-heads-retain-coordinate-q-s3-retract: that constructs the proper q-weighted corner retained by both native heads; this proves that x_84(1) ties the active coordinate weights together and, with B2 and either orientation of the first prefix bridge, leaves only scalar zero or one Cantor weights.
  endpoint-b2-enlargement-has-native-s3-retract: that kills B2 in the quotient R/pR and retains the native S3; this shows exactly why adding the constant coefficient at the same root position defeats all diagonal locally constant refinements of that escape.
  endpoint-zero-tail-packet-has-marked-finite-model: that gives a GL40(F2) model of the complete inward-outward package and retains the actual mark; this classifies the failure of the narrower Cantor-diagonal weighted-corner ansatz and records the infinite depth-growing elementary subcore inside that finite-model-safe package.
  leavitt-diagonal-compression-is-elementary-amenable: that identifies the whole Cantor diagonal and its locally finite elementary group; this uses the Cantor-function model only to solve the exact commutation equations for one active weighted corner.
  native-prefix-coefficient-core-is-rf-nonamenable: that classifies the infinite four-generator coefficient core isolated here as a nonamenable residually finite polynomial linear group; this claim supplies the corner collapse and unbounded-depth generation used by that classification.
---

**ESTABLISHED DIAGONAL-CORNER BREAKER, NOT AN MF BREAKER.**  Let `D` be the
Cantor diagonal of the binary Leavitt ring and put

```text
n=x_78(1),          m=x_87(1),          k=x_84(1),
B_2=x_84(b_2),      b_2=s_00t_1.                       (CCW1)
```

Use either one of the two first-prefix crossings

```text
A_1=x_47(a_1),      a_1=s_1t_0,
L=x_47(b_1),        b_1=s_0t_1.                       (CCW2)
```

Let

```text
Q_h=h_4E_44+h_7E_77+h_8E_88,          h_i in D       (CCW3)
```

be a diagonal projection.  If `Q_h` commutes with `n,m,k,B_2` and with
either `A_1` or `L`, then

```text
h_4=h_7=h_8=h,                    h in {0,1}.          (CCW4)
```

Thus the first constant crossing really destroys the proper
Cantor-diagonal active corner used by all preceding `S_3` retracts.  The
native roots `n,m` force `h_7=h_8`; `k` forces `h_8=h_4`.  Commutation with
`A_1` or `L` gives

```text
h(0x)=h(1x),                                           (CCW5)
```

and commutation with the depth-mismatched `B_2` gives

```text
h(00x)=h(1x).                                          (CCW6)
```

Equations `(CCW5)--(CCW6)` force the locally constant Boolean function `h`
to be constant.

This is the exact boundary requested by the coordinate-corner audit:
`x_84(1)` is not merely unsupported by the old proof; it algebraically
removes every nontrivial active weight from `D`.  It does **not** prove that
the enlarged group is non-MF, nor even that it lacks another finite quotient
or a non-diagonal reducing projection.

The coefficient core is already genuinely infinite, rather than another
finite `GL` packet.  Put

```text
c=b_2a_1=s_00t_0.                                     (CCW7)
```

Then `<n,m,A_1,B_2>` contains

```text
x_87(c^k),                  k>=1,                      (CCW8)
```

and `c^k=s_(0^(k+1))t_0` are nonzero and pairwise distinct by the Leavitt
grading.  Thus the first corner-destroying package meets an unbounded-depth
elementary core.  This still is not a same-carrier breaker:
`endpoint-zero-tail-packet-has-marked-finite-model` supplies an exact
`GL_40(F_2)` model of the whole inward-outward packet retaining the mark.
The exact follow-up `native-prefix-coefficient-core-is-rf-nonamenable`
identifies the infinite abstract core as a nonamenable residually finite
subgroup of `GL_6(F_2[t])`.  Thus the depth growth here is genuine but is
MF-safe; it is not another hidden Jacobson obstruction.

No Property `(T)`, Kazhdan input, trace profile, stability theorem,
finite-word computation, or numerical approximation is used.

DERIVATION
constant-crossing-cantor-weight-proof
