---
rg: 2
id: two-letter-dihedral-gram-row-proof
kind: route
title: Read the desired intertwining residual as one off-diagonal block of ajbj
target: two-letter-dihedral-swap-wordizes-one-gram-row
requires:
  - dihedral-spin-packet-supplies-common-partial-swap
---

On the marked D8 sector, split by the two eigenspaces of the role
involution `z`.  The swap `j` is off diagonal, whereas any letters `a,b`
commuting with `z` are block diagonal.  The elementary factorization

```text
ajbj-1=(aj-jb)bj
```

preserves Hilbert--Schmidt norm.  The upper-right block of `aj-jb` is
`AS-SB`; its lower-left block contains only the uncontrolled complementary
blocks.  Orthogonality of the two blocks gives the exact sum of squares
`(TLD5)` and hence the desired one-sided lower bound.

For exact completeness take the unused block of each occurrence letter and
each global-variable letter to be the identity.  The common tracial modular
swap then intertwines the remaining left and right blocks simultaneously,
so the literal two-letter words are exact without imposing cross-context
commutation.
