---
rg: 2
id: priority-decoder-selector-gate-lipschitz-proof
kind: route
title: Telescope the two priority partitions before comparing their gated direct sums
target: priority-decoder-lipschitz-under-selector-gate-alignment
requires: []
---

Put `S_a=(1-T_a)/2`.  Products of contractions satisfy the noncommutative
telescoping estimate

```text
||A_1...A_k-B_1...B_k||_2 <= sum_j ||A_j-B_j||_2,         (1)
```

because the usual telescoping identity has contractions multiplying every
difference on the left and right.  It does not require cross-context
commutation.  Consequently

```text
||E-F||_2 <= (1/2) sum_b ||Z_b-T_b||_2,                   (2)
```

and, by telescoping the defining products for `Q_a,R_a`,

```text
||Q_a-R_a||_2
 <= ||E-F||_2 + (1/2) sum_(b<=a)||Z_b-T_b||_2
 <= sum_b ||Z_b-T_b||_2.                                 (3)
```

Cauchy--Schwarz in the finite branch index now gives

```text
||E-F||_2^2 <= (m/4) sum_b ||Z_b-T_b||_2^2,
sum_a ||Q_a-R_a||_2^2 <= m^2 sum_b ||Z_b-T_b||_2^2.       (4)
```

For every branch,

```text
Q_aG_a-R_aH_a = Q_a(G_a-H_a)+(Q_a-R_a)H_a.
```

Left multiplication by a projection is `L^2`-contractive, and right
multiplication by the unitary `H_a` preserves the `L^2` norm.  Hence

```text
||Uhat-Vhat||_2
 <= ||E-F||_2
    +sum_a ||G_a-H_a||_2
    +sum_a ||Q_a-R_a||_2.                                 (5)
```

There are `2m+1` summands on the right.  Squaring (5), applying
Cauchy--Schwarz to those summands, and then substituting (4) proves `(PAL)`.
