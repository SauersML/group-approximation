---
rg: 2
id: rank-zero-compactness-fails-for-invertible-laurent
kind: claim
title: Rank-zero compactness fails even for one invertible Laurent equation
distinct_from:
  atlas-augmented-rank-zero-set-compactness: that is a special characteristic-two assertion for the augmented Atlas system; this is a characteristic-zero counterexample showing that no formal rank-compactness principle can prove it.
  atlas-rank-stability-literature-fence: that audits the available positive theorems; this supplies an elementary negative model for the unrestricted lifting inference.
---

Over `Q`, there are invertible matrices `U_n,V_n in GL_n(Q)` such that

```text
rank(V_n U_n-2 U_n V_n)=1,                            (RZC1)
```

and hence the normalized rank defect of the invertible Laurent equation

```text
V U V^-1 U^-1=2I                                     (RZC2)
```

tends to zero.  Nevertheless `(RZC2)` has no nonzero finite-dimensional
solution over any characteristic-zero field.

Therefore an exact point in a rank-metric matrix ultraproduct does not in
general promote to an exact finite matrix point, even with two invertible
variables and one Laurent equation.  This does not refute the special
binary Atlas claim.  It proves that
`atlas-augmented-rank-zero-set-compactness` must use special structure of
its characteristic-two packet/amalgam/fillings and cannot be obtained from
algebraic compactness, rank-ultraproduct exactness, or the finiteness of the
relation list alone.

