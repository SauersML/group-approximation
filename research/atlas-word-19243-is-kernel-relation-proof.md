---
rg: 2
id: atlas-word-19243-is-kernel-relation-proof
kind: route
title: Replay the eight-syllable word in the exact binary Leavitt algebra
target: atlas-word-19243-is-kernel-relation
requires: []
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_word_19243_trace.py
---

The committed trace script constructs the eight syllables from the named
`F_2` transvections, evaluates each chart element in the exact binary Leavitt
algebra, and multiplies them using the repository's finite prefix normal form.
No floating-point approximation is used.

The final exact predicate is

```text
leavitt_is_one(value) = true.
```

The archived collision record independently stores the same word and records
`leavitt_is_one: true`.  Therefore its image under the canonical two-chart map
is the identity, i.e. `q_19243 in ker(bar_rho)`.