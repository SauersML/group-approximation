---
rg: 2
id: thompson-v-cantor-orbits-have-no-folner-sets-proof
kind: route
title: An almost-invariant point set would give a V-invariant mean on clopen sets, and cylinders halve
target: thompson-v-cantor-orbits-have-no-folner-sets
requires: []
---

Suppose finite sets `F_n` have `max_s |sF_n Delta F_n| / |F_n| -> 0`. For a word of
length `l`, `|gF_n Delta F_n| <= l max_s |sF_n Delta F_n|`. Define, along an
ultrafilter,

```text
mu(C) = lim_omega |F_n intersect C| / |F_n|        (C clopen).
```

This is a finitely additive probability on the clopen algebra. Because
`|F_n intersect g^(-1)C| = |gF_n intersect C|` differs from `|F_n intersect C|` by at
most `|gF_n Delta F_n|`, it is `V`-invariant.

The prefix replacement `{0,10,11} -> {00,01,1}` maps the cylinder `0*` onto `00*`.
The replacement `{0,10,11} -> {01,00,1}` maps it onto `01*`. So
`mu(00*) = mu(01*) = mu(0*)`. Finite additivity gives
`mu(0*) = mu(00*) + mu(01*) = 2 mu(0*)`, so `mu(0*) = 0`, and likewise `mu(1*) = 0`.
Then `mu(Cantor set) = 0`, contradicting `mu(Cantor set) = 1`. Hence the
isoperimetric ratio in `(CF1)` is bounded below by a positive constant.
