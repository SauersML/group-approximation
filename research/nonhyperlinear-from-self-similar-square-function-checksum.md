---
rg: 2
id: nonhyperlinear-from-self-similar-square-function-checksum
kind: route
title: Apply the multiscale checksum floor to canonical matrix microstates
target: non-hyperlinear-group
requires:
  - multiscale-square-function-checksum-forces-hs-floor
  - self-similar-square-function-checksum-compiler
---

Let `Gamma` and `y!=1` be supplied by the compiler.  If `Gamma` were
hyperlinear, its canonical microstates would have defining-relator energy
tending to zero and would satisfy every fixed trace test used by the decoder.
The compiler gives `a_0>=beta-o(1)`, while the multiscale square-function
lemma and `(SSC3)--(SSC4)` give

```text
a_0<=C sqrt(K E/(1-lambda))+o(1)->0.                  (NMS1)
```

This is a contradiction.  Hence `Gamma` is non-hyperlinear.

The argument uses one fixed finite presentation and one aggregated checksum;
it does not sum an infinite family of defining relators.  The static
heavy-tail no-go explains why the recurrence and the common root carrier are
both load-bearing.
