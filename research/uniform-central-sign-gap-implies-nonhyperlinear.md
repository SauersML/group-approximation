---
rg: 2
id: uniform-central-sign-gap-implies-nonhyperlinear
kind: claim
title: A uniform finite-matrix gap on the exact negative central-sign sector implies nonhyperlinearity
distinct_from:
  central-sign-bcs-energy-decoder-implies-nonhyperlinear: that obtains the gap by decoding a robust BCS energy on a positive carrier; this is the abstract presentation-level criterion once any exact-sign gap is known.
  perfect-lcs-gap-implies-nonhyperlinear: that invokes the solution-group/game dictionary; this uses only central-sign corner exactification.
  central-packet-sign-supplies-marked-carrier: that extracts a positive approximate sign carrier from separated tuples; this uses canonical microstates, where the carrier mass converges exactly to one half.
---

**ESTABLISHED.**  Let

```text
Gamma=<S,J | R, J^2=1, [J,s]=1 (s in S)>                         (UCG1)
```

be finitely presented with `J!=1`.  Suppose there is `delta_0>0` such that
no finite-dimensional unitary tuple satisfies

```text
J=-I,              max_(r in R)||r(U)-I||_2<delta_0.              (UCG2)
```

Then `Gamma` is nonhyperlinear.

Indeed, canonical microstates would have `tau(J)->0`.  Exactifying the
approximately central involution and restricting to its negative spectral
projection gives an exact `J=-I` tuple.  The negative rank ratio tends to
`1/2`, so corner normalization multiplies every compressed defect by at most
`sqrt(2)+o(1)`.  Block-diagonal and polar correction changes the fixed
relators by `o(1)`.  The resulting finite tuple eventually violates `(UCG2)`.

The exact sign condition in `(UCG2)` is therefore harmless.  What is
load-bearing is a dimension-independent `delta_0`; exclusion only of exact
finite-dimensional representations is insufficient.

