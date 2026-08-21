---
rg: 2
id: thompson-v-one-word-ceiling-from-r5-carmichael-family
kind: route
title: Collapse the Bleak--Quick three-cycle using only a coherent Carmichael star
target: thompson-v-one-word-strict-hs-ceiling
requires:
  - thompson-v-r5-coherent-carmichael-family
  - coherent-carmichael-family-forces-thompson-three-cycle-collapse
---

Take the word `w=b=(01 10 11)`.  The compiler and compact-packing theorem give

```text
||U(b)-I||_2 <= 2 C def_R(U).
```

Hence presentation defect tending to zero forces the marked word to the
identity, which is stronger than a strict ceiling below its regular squared
HS energy `2`.  The existing binary CE-trace-face route then proves that
Thompson `V` is nonhyperlinear.

This is strictly less data than the full CAP route: it needs only the order
relations and pairwise Carmichael relations among exact conjugates of `U(b)`.
It uses neither Gowers--Hatami exactification nor a representation-dimension
bound.
