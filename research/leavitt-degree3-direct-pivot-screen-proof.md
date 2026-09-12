---
rg: 2
id: leavitt-degree3-direct-pivot-screen-proof
kind: route
title: Enumerate every one-plus-one-plus-nine cover and both literal pivots
target: leavitt-degree3-direct-pivot-screen-is-empty
requires:
  - leavitt-padded-center-template-has-no-degree2-packet
---

The topology pass enumerates all length-eleven sign words of exponent sum
three.  Exactly eleven have orbit valences `(1,1,9)`.

For each topology, the exact artifact enumerates the

```text
11!/4! = 1,663,200
```

placements of

```text
(r,e,a,c,1,b,d,p,1,1,1).
```

For each placement and each of the two unary orbits it:

1. cyclically bases the unary relator at its unique `z` occurrence;
2. solves that relation literally for `z` as a word in the three coefficient
   copies;
3. substitutes the word and its inverse at all nine stable-letter
   occurrences of the remaining orbit; and
4. reduces exactly in the faithful twenty-leaf Bergman normal form for the
   free product of the coefficient copies.

The total census is

```text
11 * 1,663,200 = 18,295,200 coefficient layouts,
36,590,400 unary-pivot substitutions.
```

MSI array job `16656967` completed topology shards one through nine.  The two
topologies initially sharing shard zero were independently resumed from
offset `850000` as shards `0/11` and `10/11`; the original shard had already
covered offsets through `800000` for each.  All exact chunks report `hits 0`.
The redundant original shard-zero tail was then cancelled, after coverage was
complete, rather than consuming further shared compute time.

The subprocess chunk size is 50,000 layouts.  This is an implementation
boundary only: every chunk runs the same exact reducer, while process exit
releases the Bergman multiplication memo table and keeps memory bounded.
