---
rg: 2
id: a5-d10-energy-paid-repair-proof
kind: route
title: Use compactness unless one sign line opens the exact A5 endpoint
target: a5-d10-parity-blocks-have-energy-paid-repair
requires:
  - a5-d10-restriction-keeps-parity-charge
---

The function `E_h` is continuous on the compact group `U(5)`.  If its zero
set is empty, it has the positive minimum `(AER3)`, while `(ADR2)` gives
`h+epsilon=res(3+3')`; choosing the exact `A_5` matrices proves
`(AER4)--(AER5)`.

If the zero set is nonempty, define

```text
f_h(t)=sup{dist(Y,Z_h):Y in U(5), E_h(Y)<=t}.
```

Compactness shows `f_h(t)->0`: otherwise a sequence with energy tending to
zero and distance bounded below has a convergent subsequence whose limit
lies in `Z_h`.

For direct sums in the nonempty branch, fix a threshold `tau`.  Blocks of
energy at most `tau` move by at most `f_h(tau)`.  The fraction of blocks
above `tau` is at most the normalized total energy times a fixed
dimension factor divided by `tau`, and unitary distance is uniformly
bounded.  First let total normalized energy tend to zero and then let
`tau` tend to zero.  This gives the asserted direct-sum modulus.  In the
empty branch, summing `(AER3)` proves `(AER6)`, and a change supported on
`O(K)` old and new dimensions has normalized Frobenius size
`O(sqrt(K/d))`.
