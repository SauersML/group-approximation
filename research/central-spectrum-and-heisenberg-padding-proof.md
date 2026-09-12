---
rg: 2
id: central-spectrum-and-heisenberg-padding-proof
kind: route
title: Use the finite cyclic spectral gap and exhibit the missing infinite cyclic gap
target: torsion-symbols-exactify-by-corners-not-infinite-symbol
requires:
  - stable-laurent-k2-has-minimal-three-symbol-packet
---

In the stable range, `c_1` and `c_2` are central and have order dividing
`m=q-1`.  Hence every eigenvalue of `pi(c_i)` is an `m`-th root of unity.
The closest nontrivial such root to `1` has distance

```text
delta_m=2 sin(pi/m).                                         (CSH1)
```

With normalized trace, spectral decomposition therefore gives

```text
||pi(c_i)-1||_2^2
 = sum_lambda |lambda-1|^2 tr(P_(i,lambda))
 >= delta_m^2 tr(1-P_i).                                    (CSH2)
```

Centrality makes each `P_i` invariant under the whole representation.  The
two projections commute, and the projection inequality

```text
1-P_1 P_2 <= (1-P_1)+(1-P_2)                                (CSH3)
```

combined with (CSH2) proves (TSE1).  Compression to `P_1P_2` is still an
exact representation and kills both torsion symbols exactly.

For the infinite-order comparison, index the standard basis modulo `n` and
define

```text
U_n e_j=e_(j+1),       V_n e_j=omega_n^j e_j.
```

A direct calculation gives

```text
U_n V_n U_n^(-1) V_n^(-1)=omega_n^(-1) 1_n.                 (CSH4)
```

Thus `u->U_n`, `v->V_n`, and `z->omega_n^(-1)1_n` is an exact
representation of the discrete Heisenberg group.  Since `omega_n!=1`, its
`z=1` spectral projection is zero, whereas

```text
|omega_n-1|=2 sin(pi/n) -> 0.                                (CSH5)
```

Now direct-sum this representation with any representation of dimension
`s_n` on which `z=1`.  The new normalized defect is

```text
sqrt(n/(n+s_n)) |omega_n-1|,                                (CSH6)
```

and its `z=1` eigenspace has dimension exactly `s_n`.  When `s_n=o(n)`,
(CSH6) still tends to zero but every invariant subspace on which the frozen
central word is exactly one occupies `o(1)` of the total dimension.  This
proves the padding firewall and also shows exactly why (CSH2) has no
infinite-order analogue without a separate spectral gap.
