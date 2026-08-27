---
rg: 2
id: atlas-a4-packet-four-rectangle-normal-form-proof
kind: route
title: Apply K2,m synchronization separately to the two packet bicliques
target: atlas-a4-packet-four-rectangle-normal-form
requires:
  - atlas-a4-packet-biclique-decomposition
  - unitary-k2m-rectangle-synchronization
---

The distinct pair graph is the disjoint union

```text
K_(2,2) disjoint_union K_(2,4).
```

Apply `unitary-k2m-rectangle-synchronization` to the first component with
`m=2`.  After its explicit tree gauge, every edge factors through row and
column gauges except for one residual whose error is exactly the unique
rectangle defect.

Apply the same theorem independently to the second component with `m=4`.
After its tree gauge, its entire factorization error is exactly the sum of
three fundamental rectangle defects.

The components are disjoint, so the two gauge choices do not interfere.
Adding the two exact squared-error identities gives `(A4-4RECT)`, with one
plus three rectangle holonomies.  The argument is algebraic and its constants
do not depend on the matrix dimension.
