---
rg: 2
id: random-coordinate-character-hash-proof
kind: route
title: Sample coordinates and average collision mass plus row cost
target: weighted-code-character-hash
requires: []
---

Choose `k_1,...,k_t` independently and uniformly.  Every two distinct
codewords differ on at least `delta L` coordinates, hence collide on the
entire sample with probability at most `(1-delta)^t`.  Therefore the
expectation of the left side of `(RCH1)` is at most `(1-delta)^tW`, while
the expectation of the left side of `(RCH2)` is `t r_bar`.

When the denominators are nonzero, divide the two random quantities by
these respective expectation bounds and add them.  Its expectation is at
most two, so one sample makes the sum at most two and hence satisfies both
displayed bounds.  Zero denominators are omitted, proving the edge cases as
well.
