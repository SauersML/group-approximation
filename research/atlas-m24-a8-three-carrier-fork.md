---
rg: 2
id: atlas-m24-a8-three-carrier-fork
kind: claim
title: Every A8 in M24 lies in an M23, M22:2, or affine 2^4:A8 carrier
distinct_from:
  atlas-a4-m23-packet-double-coset-screen: that screens pairs lying in one M23; this identifies all maximal carrier sources inside M24 and leaves cross-carrier geometry open.
  atlas-o8p2-carrier-a8-classes-and-absorption: that is the triality carrier audit in O8+(2), not the sporadic M24 carrier fork.
---

Let `A~=A8<M24`.  Then `A` is contained in a maximal subgroup of one of the
three types

```text
M23,             order 10200960,
M22:2,           order   887040,
2^4:A8,          order   322560.                     (M24C-1)
```

The official ATLAS maximal-subgroup table has exactly four rows whose orders
are divisible by `20160`: the three in `(M24C-1)` and

```text
L3(4):S3,        order   120960.                     (M24C-2)
```

The last row cannot contain `A8`.  Its normal simple socle is `L3(4)` and its
quotient has order six.  For a hypothetical `A8` subgroup, intersection with
the socle is normal in `A8`; the induced map to the quotient cannot be
injective, hence the intersection is all of `A8`.  This would embed `A8` into
the equal-order but nonisomorphic simple group `L3(4)`, an impossibility.

No assertion is made here about ambient fusion of the three remaining carrier
sources.  In particular, the existing M23 screen absorbs only pairs sharing
one M23 carrier; cross-carrier pairs in `M24` remain a new finite equality
problem.

Source: [ATLAS M24 maximal subgroups](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/).

