---
rg: 2
id: sublinear-bs-block-liftability-invariance-proof
kind: route
title: Compare the block-cut tuple in flexible HS and identify its unchanged relative lift class
target: sublinear-bs-block-surgery-is-invisible-to-relative-liftability
requires: []
---

For `P=1-Q` and a reflection `X`, the off-diagonal blocks of `X` are
supported on `Q+XQ`, of dimension at most `2 rank(Q)`.  Moreover

```text
P-(PXP)^2=PXQXP
```

is a positive contraction of rank at most `rank(Q)`.  Spectral sign
rounding therefore changes `PXP` by Frobenius norm at most
`sqrt(rank(Q))`; the same holds on `Q`.  Replacing every coordinate on the
`Q` block and padding it by `o(d)` changes the tuple by `o(1)` in flexible
normalized HS.

The two tuples consequently represent the same relative homomorphism in
the tracial matrix ultraproduct.  If exact coordinate endpoints flexibly
lift either representative, the triangle inequality makes them lift the
other; the converse is identical.  Exact torsion rounding on the passive
block changes only its representative and does not produce the missing
relative product with the fixed BS core.  Hence the block surgery leaves
relative liftability invariant.
