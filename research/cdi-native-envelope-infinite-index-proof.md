---
rg: 2
id: cdi-native-envelope-infinite-index-proof
kind: route
title: Read the untouched tensor coordinates in the relative commutant
target: cdi-native-envelope-inclusion-is-infinite-index
requires:
  - cdi-property-t-envelope-has-nonabelian-base
---

CDI Proposition 3.8 realizes the input copy as `M^e` inside the tensor base
`M^B`.  Tensor coordinates commute, hence

```text
M^(B\{e}) <= (M^e)' intersect M^B <= (M^e)' intersect Q.
```

Since `B` is infinite and `M` is a II1 factor, the left-hand algebra is
diffuse (in fact another infinite tensor factor).  For an inclusion of finite
factors with finite Jones index, the relative commutant is finite
dimensional.  The inclusion therefore has infinite index.

