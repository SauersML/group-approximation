---
rg: 2
id: closed-local-safe-tail-compactness-proof
kind: route
title: Apply the finite-intersection property in the infinite trajectory space
target: closed-local-rules-have-uniform-hitting-or-infinite-safe-tail
requires: []
---

Assume safe trajectories exist for every finite length. In `X^N`, impose the
closed cylinder conditions `x_0 in I`, `x_j in A`, and that every applicable
length-`r+1` window belongs to `C`. Every finite collection of these
conditions is realized by a sufficiently long safe trajectory. The family
therefore has the finite-intersection property, and compactness of `X^N`
gives an infinite point satisfying all conditions. The converse is immediate
by taking prefixes.
