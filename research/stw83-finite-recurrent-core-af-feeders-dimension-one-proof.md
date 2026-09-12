---
rg: 2
id: stw83-finite-recurrent-core-af-feeders-dimension-one-proof
kind: route
title: Freeze the recurrent core so every finite-stage source reaches every cycle
target: stw83-finite-recurrent-core-af-feeders-dimension-one
requires:
  - stw83-hereditary-finite-exhaustion-preserves-one
  - stw83-finite-source-dichotomy-dimension-one
---

Let `H_n` contain `K^0` and the first `n` feeder blocks.  The direction
assumptions make these finite vertex sets hereditary and exhaustive.  The induced
finite graph `E_n` has Condition (K), because every cycle lies in the full core
`K` and Condition (K) holds there.

Every source of `E_n` lies in a feeder block and reaches `K`.  Strong
connectivity of `K` then lets it reach a vertex on every cycle in `K`; these are
all the cycles of `E_n`.  Hence every source connects to every cycle, so
`stw83-finite-source-dichotomy-dimension-one` gives

```text
dim_nuc(C*(E_n)) <= 1.
```

Equivalently, at every finite stage the source ideal is stable AF and the
AF-by-O-infinity extension is full, which is precisely the color-reuse input
missing from the generic extension estimate.  Applying
`stw83-hereditary-finite-exhaustion-preserves-one` proves the upper bound for
`C*(E)`.  The core contains a cycle, so the algebra is not AF and the value is
exactly one.
