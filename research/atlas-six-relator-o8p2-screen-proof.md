---
rg: 2
id: atlas-six-relator-o8p2-screen-proof
kind: route
title: Compress all O8+(2) six-relator conjugator screens through the s_0 class fiber
target: atlas-six-relator-o8p2-has-no-marked-pair
requires:
  - atlas-six-relator-next-simple-target-is-o8p2
  - atlas-o8p2-cross-class-pairs-reduce-to-ten-marked-screens
  - atlas-six-relator-relative-small-cancellation-audit
artifacts:
  - experiments/atlas_o8p2_six_relator_screens.py
  - experiments/atlas-six-relator-o8p2-screens.json
---

The replay constructs `G=PrimitiveGroup(135,2)`, its three natural and three
orthogonal `A8` classes, and the two marking parities not absorbed by an
orthogonal `S8` normalizer.  It decodes the six literal free-product words
from the same certified source used by all preceding six-relator screens.

A tenfold loop over all `|G|=174182400` relative conjugators is unnecessary.
In every marking, the first word has the exact form

```text
s_0 = x A x C x D,                                  (S6O8R1)
```

where `A,C,D` are fixed elements of the first chart and `x=b^g` is a
conjugate of one fixed second-chart element.  The script enumerates the
conjugacy class of `b`, retains exactly the `x` satisfying `(S6O8R1)`, chooses
`g_0` with `b^g_0=x`, and replays every `z g_0` for `z in C_G(b)`.  These
fibers are disjoint and exhaust all ambient conjugators satisfying `s_0`.
An assertion checks

```text
number of replayed conjugators
  = number of class hits times |C_G(b)|.             (S6O8R2)
```

The remaining five words are then multiplied literally with exact degree-135
permutations.  Every first-failure row sums to its independently certified
`s_0` fiber.  The complete one-core Sage 10.7 replay takes about thirty-one
seconds on one Milan Sioux node and produces `(S6O8-2)` with zero survivor in
all ten screens.  No floating point, sampling, or ambient-group truncation is
used.

