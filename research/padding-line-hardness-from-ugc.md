---
rg: 2
id: padding-line-hardness-from-ugc
kind: route
title: Instantiate UGC at eps = 1/4, whose point (3/4, 1/4) lies below the padding line
target: unique-games-np-hard-below-the-padding-line
requires: [unique-games-conjecture]
---

Immediate. `unique-games-conjecture` at `eps = 1/4` gives an alphabet `K` with
`Gap-UG_K[3/4, 1/4]` NP-hard. Since `1/4 < 2(3/4) - 1 = 1/2`, this is a witness,
with deficit ratio `3`. The arithmetic is item 4 of
`ug-hardness-deficit-ratio-padding-line`, which is not needed as a premise.

The route records a **necessity** arrow. It makes the milestone
`unique-games-np-hard-below-the-padding-line` a prerequisite that can fail on
its own: an algorithm for any gap below the padding line refutes the
conjecture.
