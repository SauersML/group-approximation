---
rg: 2
id: root-additivity-eliminates-the-s3-rank-one-leak
kind: claim
title: Literal root additivity eliminates every S3 realization of the rank-one denominator leak
distinct_from:
  rank-one-self-commutator-coboundary-packet-has-s3-leak: that gives an S3 leak when X, Y, and C are independent variables; this proves that no such leak survives after they are built from two literal root variables centralized by U.
  sl3-rank-one-denominator-self-commutator-removes-target-phase: that gives a dimension-free phase-removal estimate in arbitrary matrices but assumes projective target control; this is an exact finite-group exclusion at the first stronger algebraic layer and gives no general matrix estimate.
  one-root-p3-denominator-fragment-has-finite-regular-leaks: that retains a root-scaling relation but not the rank-one Weyl decomposition from the same two opposite-root variables; this checks exactly that joint packet in the smallest finite enemy S3.
---

Let `u,h,a,b in S_3` satisfy

```text
[u,a]=[u,b]=1                                             (RAS1)
```

and the literal root-additive form of the rank-one denominator identity

```text
h=a^2 (h b^(-2) h^(-1)) a b a^(-1).                     (RAS2)
```

Then

```text
[u,h]=1.                                                  (RAS3)
```

Indeed `(RAS2)` is exactly `H=X(HYH^*)XC` after substituting

```text
X=a^2,       Y=b^(-2),       C=a^(-1)b a^(-1).           (RAS4)
```

Thus the six-dimensional regular `S_3` leak cannot be repaired into a
countermodel once the three lattice words are required to come from the same
two opposite-root variables and `U` centralizes those variables.

This is only a smallest-enemy exclusion. It does **not** say root additivity
suffices in arbitrary finite groups or matrices, and it does not yet use a
genuine rank-two Steinberg relation. The next exact falsification target is
therefore `(RAS1)--(RAS2)` in larger finite groups; only after that packet
survives should one add the rank-two shared-root identity
`a=[x_12(1),x_23(1)]` (and its opposite-root mate) on the same carrier.

