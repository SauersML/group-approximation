---
rg: 2
id: small-cut-hs-does-not-control-terminal-operator
kind: claim
title: Vanishing individual cut HS scale does not make the terminal seam operator-small
distinct_from:
  nested-common-cuts-have-exact-pythagorean-boundary-ledger: that proves the exact sum of squared cut boundaries; this shows that small summands do not control the operator norm of their aggregate.
  full-dyadic-split-tree-has-an-extensive-terminal-seam: that detects an extensive rank-remainder seam in a full dyadic replication tree; this gives an explicit reflection/pinching example with every individual cut boundary tending to zero.
---

ESTABLISHED.  For every `N` there is a reflection `Q_N` and a nested common
cut tree such that every individual cut boundary has squared normalized
Hilbert--Schmidt norm at most `1/N`, while for the terminal pinching `Phi_N`

```text
O_N=Q_N-Phi_N(Q_N)=Q_N,
||O_N||_op=1,
||O_N||_2^2=1.                                        (SCS1)
```

Thus neither a vanishing maximum of the individual HS cut costs nor exact
Pythagorean accounting of their sum implies
`max_i||Q_i-Phi(Q_i)||_op=o(1)` or
`||L^(-1)sum_i O_i^2||_op=o(1)`.  Spike quarantine as currently stated
controls the trace of explicitly detected witness supports, not this
aggregate terminal operator seam.
