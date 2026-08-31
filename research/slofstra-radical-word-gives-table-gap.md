---
rg: 2
id: slofstra-radical-word-gives-table-gap
kind: route
title: Haarize the Slofstra tracial image and expose one radical word
target: regular-finite-table-quantum-classical-hamming-gap
requires:
  - slofstra-tracial-image-has-radical-word
  - sofic-radical-soficization
  - character-diracization-limit
  - ce-characters-closed-multiplicative-semigroup
---

Let `H=S/N` be `(STI1)`. Put `psi=(1+chi)/2`. Equality in the triangle
inequality gives

```text
|psi(g)|=1  iff  chi(g)=1  iff  g in N.
```

The character `psi` is Connes embeddable by convexity, and
`ce-characters-closed-multiplicative-semigroup` keeps every
`|psi|^(2m)` and its pointwise limit Connes embeddable.
`character-diracization-limit` identifies that limit with `1_N`, the regular
character of `H`. Thus `H` is hyperlinear. If `(STI2)` holds, then
`Rad_sof(H)` is nontrivial, so
`sofic-radical-soficization` says `H` is not sofic.

By the local definitions, nonsoficity supplies one finite multiplication
window and a positive Hamming defect floor for every permutation model,
while hyperlinearity supplies arbitrarily accurate regular-character unitary
models of that same window. This is exactly
`regular-finite-table-quantum-classical-hamming-gap`.
