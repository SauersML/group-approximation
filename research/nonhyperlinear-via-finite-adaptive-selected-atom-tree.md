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
`sqrt(2)` from the identity.  Thus `Q_-` has asymptotic trace `1/2`, and the
Pauli `B`-half used for the seed has asymptotic ambient trace `1/4`, not
merely an unspecified positive trace.

At each reached node, `(MFA1)` and `(FAT1)` give

```text
tau(Q_(sigma i))
 >=(1+eta beta/M)tau(Q_sigma)-C' sqrt(E).
```

There are only `N` steps, so all accumulated constants are fixed.  With
`N` chosen by `(FAT2)`, the terminal carrier has trace strictly larger than
one when the relator energy tends to zero, a contradiction.  The exact
finite-tracial BCS model extends by the consistency clause of the adaptive
tree and keeps `J=-1`, so the marked word is nontrivial.
