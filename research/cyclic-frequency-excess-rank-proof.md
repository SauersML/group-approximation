---
rg: 2
id: cyclic-frequency-excess-rank-proof
kind: route
title: Sum the lowest cyclic frequencies by Ky Fan
target: cyclic-frequency-ledger-pays-excess-source-rank
requires:
  - bs14-source-mode-reset-has-exact-frequency-cost
---

Let `A=|R-1|^2` and `P=WW^*`.  Ky Fan's minimum principle bounds
`F=Tr(PA)` below by the sum of the `k` least eigenvalues of `A`.  The zero
frequency has multiplicity `n`.  If `q=max(k-n,0)`, the `l`-th subsequent
cyclic distance satisfies `d_l>=l/(2n)`, including the single terminal shell
when `m` is even.  Therefore

```text
sum_(l=1)^q d_l^2 >= q^3/(12n^2).
```

Since `4sin^2(pi d/m)>=16d^2/m^2` for `0<=d<=m/2`, this gives

```text
F >= (4/3)q^3/(n^2m^2),
q/(mn) <= ((3/4)F/(mn))^(1/3).
```

The cited exact reset theorem gives capacity at most one neutral source per
scalar cycle, hence at most `n` per multiplicity-`n` packet.  Deleting the
remaining `q` source directions has squared normalized Frobenius cost
`q/(mn)`, proving the sixth-root estimate.  Deleting the final at-most-`n`
capacity directions costs at most `m^(-1/2)` in normalized norm; the triangle
inequality yields `(CFR7)`.  The cases `q=0` and `m=1` obey the same formulas.
