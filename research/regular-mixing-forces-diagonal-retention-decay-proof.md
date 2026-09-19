---
rg: 2
id: regular-mixing-forces-diagonal-retention-decay-proof
kind: route
title: Mix with the regular trace and apply the fusion Rayleigh coefficient
target: regular-mixing-forces-diagonal-retention-decay
requires:
  - diagonal-retention-fusion-coefficient
---

The convex decomposition `(RMD1)` gives positive-functional domination
`epsilon theta<=tau_epsilon`.  CE passes from a tracial algebra to every
GNS algebra of a dominated trace, so non-CE of `theta` implies non-CE of
`tau_epsilon`.  The regular term vanishes off the identity, giving
`|tau_epsilon(g)|<=epsilon` there.  Thus its scalar kernel is `{e}` and its
pointwise tensor powers converge to `delta_G`.  The limiting canonical
algebra is `L(G)`, which is CE by hyperlinearity.  Equation `(DRC6)` now
gives `d_n(tau_epsilon)->0`.
