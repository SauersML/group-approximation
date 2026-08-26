---
rg: 2
id: b2-b3-pair-full-hecke-four-native-sectors
kind: claim
title: The B2 and B3 arms quarter the full Hecke source into the four native sign sectors
artifacts:
  - research/b2-b3-full-hecke-four-sector-proof.md
distinct_from:
  b2-pairs-full-hecke-first-support: that uses B2 alone to split the first native r sign exactly in half; this adds the B3 flip of the second native t sign and proves that the two actual compression supports meet in exactly one quarter of Q.
  native-j1-extension-gives-gl5-but-only-second-whitehead-gram: that obtains only a one-third lower bound for the second support on the coarser p2 source and leaves the first sign free; this obtains sharp one-half marginals and a sharp one-quarter joint sector on the finer actual source Q.
  full-moving-hecke-packet-retains-q-kernel-profile: that proves the endpoint compression QWQ can vanish; this concerns the internal joint r,t decomposition of Q and is compatible with W carrying Q orthogonally outside itself.
  full-hecke-quarter-source-equalizes-selector-ranks: that inserts these sharp ranks into the affine selector formula and proves that normalization on Q changes the two source fractions to one half and one half; this establishes only the four-sector geometry.
---

**ESTABLISHED REPRESENTATION-UNIVERSAL JOINT SUPPORT.**  On the actual
common Hecke source

```text
Q=e_(L_0,lambda_0)
```

put

```text
r=x_58(a_2),      t=x_69(a_3),
B_2=x_84(b_2),    B_3=x_95(b_3),
C_2=x_54(q),      C_3=x_65(q).                       (BQS1)
```

All four of `r,t,B_2,B_3` normalize the signed pair defining `Q`.  The
ordinary Steinberg rows give

```text
[r,B_2]=C_2,       [t,B_3]=C_3,
[r,t]=[t,B_2]=1,   C_2Q=C_3Q=-Q.                     (BQS2)
```

Thus `B_2Q` flips the `r` sign while preserving the `t` sign, and `B_3Q`
flips the total `t` sign.  For `epsilon,delta in {+1,-1}`, define

```text
E_(epsilon,delta)
  =Q(1+epsilon r)(1+delta t)/4.                       (BQS3)
```

In every exact finite-dimensional representation of the packet,

```text
rank(E_(epsilon,delta))=rank(Q)/4                     (BQS4)
```

for all four choices of signs.  In particular the two actual native
compression supports restricted to `Q` are

```text
QJ_1p_2J_1Q=Q(1+r)/2,
QJ_2p_2J_2Q=Q(1+t)/2,                                (BQS5)
```

and their common source intersection is

```text
F=Q(1+r)(1+t)/4,
rank(F)=rank(Q)/4.                                   (BQS6)
```

This is a literal same-matrix positive carrier for the two native
Whitehead compression occurrences.  It is not inferred from canonical
trace and is not a statement about the endpoint word `W`.  In particular,
`QWQ=0` can coexist with `(BQS4)--(BQS6)`.

No Property `(T)`, canonical trace, computation, literature input, or
Lean compilation is used.

DERIVATION
b2-b3-full-hecke-four-sector-proof
