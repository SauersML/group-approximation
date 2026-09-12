---
rg: 2
id: mixed-intertwiner-energy-transport-localization-proof
kind: route
title: Orthogonal block decomposition turns intertwining energy into transport cost
target: mixed-intertwiner-energy-transport-localization
requires: [unitary-block-energy-transport]
---

The transportation statement is `unitary-block-energy-transport`, applied to
`P_i`, `Q_j` and `U`: orthogonality gives the two marginals exactly.

For the energy inequality, write

```text
T_(i,j)=P_i U Q_j.
```

Because `P_i` reduces `rho` and `Q_j` reduces `sigma`, for every `s in S`

```text
P_i (rho(s)U-U sigma(s)) Q_j
 = rho(s)T_(i,j)-T_(i,j)sigma(s).
```

The rectangular operator spaces `P_i M_d Q_j` are pairwise orthogonal for the
Hilbert--Schmidt inner product.  Hence, for each `s`, Pythagoras gives

```text
||rho(s)U-U sigma(s)||_2^2
 = sum_(i,j) ||rho(s)T_(i,j)-T_(i,j)sigma(s)||_2^2.
```

Summing over `s` and using the definition of `lambda_(i,j)` on every nonzero
block yields

```text
E(U)
 >= sum_(i,j) lambda_(i,j) ||T_(i,j)||_2^2
 =  sum_(i,j) lambda_(i,j) m_(i,j).
```

Finally, on the set where `lambda_(i,j)>=a`, every summand in the last display
is at least `a m_(i,j)`.  Therefore

```text
a sum_(lambda_(i,j)>=a) m_(i,j) <= E(U),
```

which is the threshold estimate.  No representation-stability theorem,
commutant approximation, or dimension estimate is used.
