---
rg: 2
id: pauli-braiding-test-exponential-dimension
kind: claim
title: Constant-success Pauli braiding forces exponential local dimension
distinct_from:
  marked-clifford-table-exponential-dimension: that starts from a complete all-pairs approximate multiplication map and uses Gowers--Hatami exactification; this starts from a succinct constant-robust nonlocal test and uses Schmidt rank.
  anchored-quantum-parallel-repetition: that amplifies a pre-existing game-value gap under repetition; this is a rigidity/dimension witness for one Pauli test and does not repeat a game.
---

There are universal constants `eta_0,c_0>0` such that for every `N`, any
finite-dimensional strategy for the perfect-complete `N`-qubit Pauli braiding
test with success at least `1-eta_0` has each player's local dimension `d`
satisfying

```text
d >= c_0 2^N.                                                  (PBD1)
```

Consequently, after being told a candidate local dimension `D`, choosing

```text
N > log_2(D/c_0)                                               (PBD2)
```

makes success `1-eta_0` impossible in that same dimension.  The acceptance
threshold and `c_0` do not deteriorate with `N`.

