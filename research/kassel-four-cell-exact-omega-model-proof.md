---
rg: 2
id: kassel-four-cell-exact-omega-model-proof
kind: route
title: Tensor a four-point permutation transport packet with a six-clock scalar commutator
target: kassel-four-cell-has-exact-omega-model
requires: []
artifacts:
  - research/artifacts/kassel-four-cell-exact-omega-model-2026-08-21.md
---

Take permutations

```text
a=(2 3), b=(0 2)(1 3), d=(0 1)(2 3), A=(1 3 2).
```

They satisfy `[a,b]=d`, `d^2=b^2=1`, and `[d,A]=b^(-1)`.
Tensor their permutation matrices with the order-six Weyl pair `X,Z`
satisfying `[X,Z]=qI`, where `q=exp(pi i/3)`.  Set
`x_(-beta)=nu I` with `nu=exp(-pi i/6)`.  The assignment in the artifact
checks all four Kassel relations exactly, while
`w_beta^4=nu^(-4)I=omega I`.

