---
rg: 2
id: pairwise-gram-cover-countermodel
kind: route
title: Give each context pair its own orthogonal block
target: pairwise-cross-grams-do-not-supply-one-game-state
requires: []
---

Let `H` be the direct sum of equal nonzero blocks `H_(cd)` indexed by
unordered context pairs, and let `Q_c` be the sum of all blocks incident to
`c`.  Then the `Q_c` commute and, for normalized trace,

```text
tau(Q_c)=2/k,
tau(Q_cQ_d)=1/binom(k,2)>0,
sum_c Q_c=2I.
```

The block projection `G_(cd)=1_(H_(cd))` is a positive exact cross-Gram
carrier on which the measurements for contexts `c,d` can be identical and
perfect.  Yet `meet_c Q_c=0`.  Moreover every density matrix `rho` obeys

```text
(1/k)sum_c tr(rho Q_c)=2/k.
```

Thus no state is supported on every certified carrier, despite exact
pairwise consistency everywhere.  Common amplification preserves the
counterexample.
