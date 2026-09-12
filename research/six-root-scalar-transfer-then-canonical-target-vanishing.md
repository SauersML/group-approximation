---
rg: 2
id: six-root-scalar-transfer-then-canonical-target-vanishing
kind: route
title: Transport the six-root scalar and invoke canonical trace at the staggered target
target: arithmetic-hexagon-decoding-or-conductor-leakage
requires:
  - rank-one-last-layer-induced-tower-avoids-six-root-carrier
---

**INVALIDATED.**  The proposed endpoint was to transport only the scalar
sixfold parity coefficient through `h`, use
`six-root-top-parity-transports-to-staggered-negative-triple` to identify its
target, and then invoke canonical trace to make that target coefficient
vanish.

The target is a word whose three root parameters grow with conductor.
Canonical convergence controls each fixed abstract group word, not such a
moving sequence.  More sharply,
`rank-one-last-layer-induced-tower-avoids-six-root-carrier` gives genuine
finite congruence representations with canonical fixed-word character and
sixfold parity trace exactly `3/7`.  Scalar transport would only force the
moving staggered target to have trace near `3/7`; there is no canonical-trace
contradiction.

Thus the remaining proof must transport a supported carrier on one
`h`-compatible reservoir, or turn failure of that supported transport into
first-exit/conductor leakage.  A scalar moment estimate by itself cannot
close the arithmetic hexagon gate.
