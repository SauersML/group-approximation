---
rg: 2
id: fixed-cut-order-seven-leakage-audit-proof
kind: route
title: Audit every existing fixed finite-coordinate cut against the order-seven leakage operator
target: fixed-cuts-do-not-control-order-seven-leakage
requires:
  - order-seven-anchor-stops-at-whitehead-compression-leakage
  - fixed-type-and-raw-rank-selectors-do-not-evade-hecke-firewall
  - middle-index-heisenberg-packet-is-not-center-chain-invariant
  - nine-pair-marked-heisenberg-regularization-is-selector-spectator
  - binary-leavitt-finite-actor-minimal-atom-dichotomy
  - one-anchor-odd-spike-has-a-cheap-reducing-cut
---

The first five conclusions are exactly the scoped conclusions of the six
required claims.  It remains only to record why spectral coarea does not
estimate the missing mass and to make the regular obstruction quantitative.

For a positive contraction sum `0<=L<=2Q`, write

```text
L=L 1_([0,t])(L)+L 1_((t,infinity))(L).
```

Taking traces and using the two operator bounds on the summands gives

```text
tau(L)<=t tau(Q)+2 tau(Q 1_((t,infinity))(L)).         (1)
```

Rearranging proves `(FLC3)`.  The established regular calculation has
`tau(L)>0`, although all fixed word relators, including the seventh powers,
have zero defect.  Hence no estimate of the form `(FLC2)` follows from those
fixed tracial data.

The coarea theorem selects a threshold with small commutator boundary in
terms of the covariance or high spectral first moment already present.  It
does not bound `tau(1_((t,infinity))(L))` from relation defect.  If one takes
the low spectral complement as the desired source cut, proving that it loses
`o(1)` mass is exactly `(FLC2)`.  This proves the stated circularity without
excluding a future moving finite-coordinate tail estimate.
