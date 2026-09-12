---
rg: 2
id: atlas-o8p2-carrier-a8-classes-and-absorption-proof
kind: route
title: Classify the three local O8+(2) A8 carriers before cross-family screening
target: atlas-o8p2-carrier-a8-classes-and-absorption
requires:
  - atlas-o8p2-a8-marked-carrier-fork
  - atlas-a8-index-33-to-89-is-orthogonal-sp6
  - atlas-a4-sp6-packet-collision-screen
  - atlas-natural-a8-supports-collapse-before-collision
---

The `S6(2)` statement and its normalizer are the established orthogonal-class
classification.  The `A9` statement is the standard degree-nine restriction:
a faithful `A8` action of degree nine has orbit profile `8+1`, hence is a
natural point stabilizer.

For `2^6:A8`, realize the orthogonal module as

```text
{x in F2^8 : sum x_i=0} / <(1,...,1)>.
```

The attached replay constructs the affine group on its 64 vectors and asks
GAP for complement-class representatives of the translation subgroup.  It
asserts carrier order 1290240, exactly two complement classes, complement
orders 20160, normalizer orders 20160, and the two orbit profiles `(O8L1)`.
The normal-subgroup argument shows that this is the complete local A8 list.

Finally place a centralizing pair in a maximal subgroup and apply the complete
carrier fork.  Each local centralizer is trivial, proving `(O8L2)`.

