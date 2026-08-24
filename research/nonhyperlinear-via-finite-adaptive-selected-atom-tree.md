---
rg: 2
id: nonhyperlinear-via-finite-adaptive-selected-atom-tree
kind: route
title: Iterate the bounded selected-atom decision tree past total trace one
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - maximal-forbidden-atom-has-a-named-positive-half
  - finite-depth-adaptive-selected-atom-escape-tree
---

In a canonical hyperlinear approximation the central involution `J` must
have trace tending to zero, hence normalized-HS distance tending to
`sqrt(2)` from the identity.  The Pauli seed therefore has asymptotic trace
`1/2`, not merely an unspecified positive trace.

At each reached node, `(MFA2)` and `(FAT1)` give

```text
tau(Q_(sigma i))
 >=(1+eta beta/(2M))tau(Q_sigma)-C' sqrt(E).
```

There are only `N` steps, so all accumulated constants are fixed.  With
`N` chosen by `(FAT2)`, the terminal carrier has trace strictly larger than
one when the relator energy tends to zero, a contradiction.  The exact
finite-tracial BCS model extends by the consistency clause of the adaptive
tree and keeps `J=-1`, so the marked word is nontrivial.
