---
rg: 2
id: canonical-iwahori-failure-is-a-regular-square-root-odd-mode
kind: claim
title: A canonical Iwahori projection failure is a regular-character positive-density square-root odd mode
distinct_from:
  iwahori-transfer-reduces-to-square-root-block-mixing: that normalizes an arbitrary failed transfer sequence; this records its regular-character presentation, which tensor camouflage shows can be imposed on every failure.
  canonical-iwahori-projection-commutant-transfer: that is the open exclusion theorem; this gives its exact matrix-ultraproduct counterexample normal form.
---

If `canonical-iwahori-projection-commutant-transfer` fails, then after a
vanishing perturbation and passage to a tracial matrix ultraproduct there are
unitaries `X,Y`, a projection `P`, and a trace-preserving embedding

```text
rho:L(SL_2(Z[1/2])) -> M=prod_omega M_(d_n)           (CRS1)
```

whose two modular vertices are

```text
(X^2,Y),                  (X,Y^2),                    (CRS2)
```

with matched central word, and

```text
[P,X^2]=[P,Y]=0,          [P,X]!=0.                  (CRS3)
```

The matrix representatives of `P` and `1-P` have traces bounded below by
one constant.  For `V=2P-1` and

```text
W=XVX^*, E=(V+W)/2, A=(V-W)/2,                       (CRS4)
```

the selfadjoint odd mode `A` has positive `L^2` norm, anticommutes with `E`,
satisfies `E^2+A^2=1`, and is negated by `Ad_X`.  Conversely, excluding this
configuration for trace-preserving, vertex-liftable embeddings proves the
canonical projection-transfer claim.

Thus the HNN route presents the exact remaining object as a macroscopic odd
square-root mode inside the canonical correspondence of the Iwahori amalgam.
This is a useful normal form, not a weaker theorem: regular tensor camouflage
places every all-character failure in this sector.
