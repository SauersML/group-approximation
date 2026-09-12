---
rg: 2
id: atlas-o8p2-cross-class-pairs-reduce-to-ten-marked-screens
kind: claim
title: The O8+(2) equality residue reduces to six subgroup-pair orbits and ten marked screens
distinct_from:
  atlas-o8p2-has-six-triality-a8-classes: that classifies individual A8 subgroups; this classifies ordered pair families after triality, inversion, carrier absorption, and marking parity.
---

Write the three natural self-normalized classes as `N_i` and the three
orthogonal `S8`-normalized classes as `O_i`, for `i in {1,2,3}`.  The outer
triality group `S3` acts simultaneously on the indices.  Swapping the two
charts identifies a pair family with its inverse.  The thirty ordered
distinct-class families therefore reduce to four orbits:

```text
N_i--N_j, i!=j;              O_i--O_j, i!=j;
N_i--O_i;                    N_i--O_j, i!=j.         (O8P1)
```

The six diagonal families reduce to two more orbits:

```text
N_i--N_i outside their unique common A9 carrier;
O_i--O_i outside their unique common S6(2) carrier. (O8P2)
```

The omitted parts of the diagonals are exactly the already absorbed cells.
Each `N_i` subgroup lies in one `A9` of its associated class, containing nine
natural `A8` point stabilizers.  Each `O_i` lies in one `S6(2)` of its
associated class, containing thirty-six orthogonal `A8` subgroups.  No
distinct-class family is absorbed by those same-carrier theorems.

Marking parity is load-bearing.  Since `N_G(N_i)=A8`, an ambient conjugator
does not realize the graph automorphism, so every orbit in `(O8P1)`--`(O8P2)`
that involves `N` requires two relative graph-parity screens.  Since
`N_G(O_i)=S8`, the orthogonal normalizer absorbs both parities.  Thus the six
subgroup-pair orbits require exactly

```text
2 + 1 + 2 + 2 + 2 + 1 = 10                         (O8P3)
```

marked representative screens.  This is the smallest screen list before
using packet relations; collapsing the two affine complement types or
discarding the natural graph parity is invalid.

