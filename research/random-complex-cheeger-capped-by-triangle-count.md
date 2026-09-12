---
rg: 2
id: random-complex-cheeger-capped-by-triangle-count
kind: claim
title: In the mid-range the permutation cocycle Cheeger constant is at most a constant over the triangle count
distinct_from:
  random-complex-cocycle-cheeger-beats-triangle-count: that is the Chapman--Peled threshold hypothesis; this is its refutation for every mid-range exponent, which is the expected answer if random Kazhdan hyperbolic groups are residually finite
  finite-quotient-caps-cocycle-cheeger-constant: that is the deterministic cap at one pair given a detecting quotient; this is the a.a.s. conclusion for random complexes, which still needs detecting quotients to exist
---

**OPEN.** For every `0 < η < 1/2`, with `p = n^(-1+η)` and `Y ~ Y(n,p)`, a.a.s.

```text
h_1(Y, Sym) = O(n^(-3) p^(-1)).
```

This refutes `random-complex-cocycle-cheeger-beats-triangle-count` for every
exponent, and so kills the Chapman--Peled route to a nonsofic hyperbolic group.
The only recorded way to reach it goes through finite quotients:
`random-complex-cheeger-capped-via-detecting-quotient`.
