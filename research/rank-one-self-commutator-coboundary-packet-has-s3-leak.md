---
rg: 2
id: rank-one-self-commutator-coboundary-packet-has-s3-leak
kind: claim
title: Even the full raw rank-one coboundary packet has an exact S3 leak
distinct_from:
  sl3-self-commutator-overlap-packet-has-s3-leak: that retains only the derived relations on W, X, and Z; this retains the original variables U and H, all three U-centralities, the conjugacy Z=HYH inverse, and the rank-one denominator decomposition H=XZXC.
  sl3-rank-one-denominator-self-commutator-removes-target-phase: that derives the self-commutator identity from a full approximate arithmetic assignment; this proves that the complete raw data used in that derivation still do not imply projective transfer.
  one-root-p3-denominator-fragment-has-finite-regular-leaks: that uses finite quotients of a Baumslag--Solitar root-scaling group; this is a six-dimensional exact permutation model of the dyadic Weyl-decomposition/coboundary packet.
---

The following entire raw packet from the proof of the rank-one denominator
self-commutator identity has an exact finite-dimensional leak. There are
unitaries `U,H,X,Y,C` and, on putting

```text
Z=H Y H^*,             W=U H U^* H^*,                  (RCB1)
```

one has

```text
[U,X]=[U,Y]=[U,C]=1,
H=X Z X C,
|tr(W)|=0.                                                (RCB2)
```

The model can be taken to be the six-dimensional left regular
representation of `S_3`. Consequently no projective-transfer estimate can
follow from the rank-one Weyl decomposition, the coboundary form of the
target, and the three lattice-word centralities alone, even at zero defect.

This locates the earliest explicit candidate for additional arithmetic input
omitted by that packet.
The actual elements are not independent: if `a=x(1)` and `b=y(1)` in the
`(1,3)` root copy, then

```text
X=a^2,       Y=b^(-2),       C=a^(-1)b a^(-1).          (RCB3)
```

Those root elements are also glued to the other four roots of `SL_3(Z)`.
The `S_3` model below violates this shared root-additivity data: its `X` is
a transposition and hence has no square root in `S_3`.  An inequality
formulated only in the five raw variables of `(RCB1)--(RCB2)` is therefore
false.  A viable estimate must use some additional arithmetic datum;
common-root additivity and cross-root gluing are the first concrete omitted
candidates, not assertions already known to suffice.
