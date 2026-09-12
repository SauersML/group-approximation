---
rg: 2
id: thompson-v-not-hyperlinear-from-one-word-ceiling
kind: route
title: A strict one-word Hilbert--Schmidt ceiling makes Thompson's V nonhyperlinear
target: thompson-v-not-hyperlinear
requires: [thompson-v-one-word-strict-hs-ceiling, thompson-v-ce-one-word-trace-face-is-binary]
---

Assume `V` is hyperlinear and fix one finite presentation `V=<X|R>` and one
word `w != 1`. An injective homomorphism into a tracial matrix ultraproduct
gives unitary tuples `U_n` with relator defects tending to zero. By
`thompson-v-ce-one-word-trace-face-is-binary` the limiting trace is
`t tau_reg + (1-t) tau_triv` with `t>0`, and after cutting to the regular
central summand and re-amplifying one may take `t=1`. Then

```text
||w(U_n)-I||_2^2 = 2 - 2 Re tr(w(U_n)) -> 2,
```

contradicting the strict bound `(TV2)` of `thompson-v-one-word-strict-hs-ceiling`.

This is the argument of `nonhyperlinear-thompson-v-from-one-word-ceiling`,
stopped at `V` instead of being spent directly on `non-hyperlinear-group`, so
that the Steinberg branch route
`thompson-v-nonhyperlinearity-selects-stable-steinberg-branch` can consume it.
