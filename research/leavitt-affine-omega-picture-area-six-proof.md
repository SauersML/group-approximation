---
rg: 2
id: leavitt-affine-omega-picture-area-six-proof
kind: route
title: Enumerate affine-Omega signed ribbons in faithful Bergman normal form
target: leavitt-affine-omega-one-copy-picture-area-at-least-eight
requires:
  - leavitt-degree-four-affine-omega-candidate
---

The artifact substitutes the four exact affine orbit relators `(A8.3)` into
the established signed-ribbon enumerator.  Equality inside each coefficient
copy is evaluated in the faithful twenty-leaf Bergman chart of the binary
Leavitt algebra; equality between copies is reduced in their free product.
The target filter is

```text
Omega(c_0,p_0)=[c_0,p_0^2 c_0 p_0^(-2)].
```

The complete counts are

```text
area  type multisets  connected planar ribbons  Omega disks  one-copy disks
  2         16                   32                  0              0
  4        100                 3240                  0              0
  6        400              1107144                  0              0
```

The area-six census was split into eight congruence shards on MSI job
`16658774`.  Their type-multiset counts

```text
47,53,48,50,55,43,54,50
```

sum to all 400 possible multisets, and their planar counts sum to the number
displayed above.  Every shard reports zero target disks and, more strongly,
zero disks with any nonidentity one-copy boundary.

Each orbit relator has valence one or three.  A picture with an odd number of
cells therefore has an odd total number of stable-letter half-edges and
cannot pair them.  Areas one, three and five are impossible, completing the
bound through area seven.
