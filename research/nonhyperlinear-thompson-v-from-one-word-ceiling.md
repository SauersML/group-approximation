---
rg: 2
id: nonhyperlinear-thompson-v-from-one-word-ceiling
kind: route
title: Use the binary Thompson-V trace face to turn one strict word ceiling into nonhyperlinearity
target: non-hyperlinear-group
requires:
  - thompson-v-one-word-strict-hs-ceiling
  - thompson-v-ce-one-word-trace-face-is-binary
---

Assume `V` hyperlinear and choose canonical regular-character microstates
`U_n`. Since `w!=1`, canonical moment convergence gives

```text
||w(U_n)-I||_2^2=2-2 Re tr(w(U_n))->2.
```

Their finite-presentation relator defects tend to zero, contradicting the
strict bound `(TV2)`. The binary character theorem shows more: a strict
ceiling below `2` rules out every nontrivial CE trace of `V`, not only the
canonical regular trace.
