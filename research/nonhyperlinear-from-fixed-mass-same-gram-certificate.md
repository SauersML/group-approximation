---
rg: 2
id: nonhyperlinear-from-fixed-mass-same-gram-certificate
kind: route
title: Apply the finite game gap directly to one fixed-mass word-controlled Gram
target: non-hyperlinear-group
requires:
  - oracularizable-tracial-nonru-game-exists
  - one-gram-vector-decodes-a-finite-bcs-strategy
  - lin-state-local-gh-is-an-intertwining-exactifier
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - labelled-pvm-branch-gram-gives-lin-corner
  - positive-cross-gram-state-rounds-to-common-pvm
  - fixed-mass-same-gram-mixed-word-certificate
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
---

Let `theta<1` be the finite-dimensional value bound for the fixed source
game. Exact completeness gives a representation with `J!=I`, so `J` is a
nontrivial abstract group element. If `Gamma` were hyperlinear, its
canonical-trace microstates would have `tau(J)->0`, hence

```text
liminf ||G||_2^2>=m_0/2.                              (SMR1)
```

The certificate gives `E_G=o(1)`. But
`one-gram-vector-decodes-a-finite-bcs-strategy` gives the dimension-free
Rayleigh inequality

```text
E_G>=(1-theta)||G||_2^2.                              (SMR2)
```

Equations `(SMR1)--(SMR2)` contradict each other. Therefore `Gamma` is not
hyperlinear. The Lin and block-Gram dependencies justify that the proposed
certificate needs only one positive state-local Gram and its mixed rows;
they are not being used to infer word visibility or mass.

