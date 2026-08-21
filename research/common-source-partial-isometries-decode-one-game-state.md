---
rg: 2
id: common-source-partial-isometries-decode-one-game-state
kind: claim
title: Separate context partial isometries with one initial projection decode one game state
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that converts one intertwining row for one partial isometry to an ordinary commutator; this proves that the partial isometry may depend on the context as long as every context has the same initial projection.
  one-gram-vector-decodes-a-finite-bcs-strategy: that uses one literal matrix Gram operator in every context; this pulls different context ranges back to one common source Hilbert space and obtains the same finite-game gap.
  pairwise-cross-grams-do-not-supply-one-game-state: that gives an exact countermodel when the source state changes from edge to edge; this shows that different ranges are harmless and identifies the common initial projection as the actual load-bearing datum.
---

For a BCS game of value at most `theta<1`, context-dependent partial
isometries `S_c` may have different ranges, provided they share one initial
projection `Q`.  Pulling every context PVM back through `S_c` gives one legal
strategy on `Q`, and its total forbidden/consistency energy satisfies

```text
E_Q >= (1-theta) tau(Q).
```

The common source, not a common range or common swap, is the load-bearing
datum.
