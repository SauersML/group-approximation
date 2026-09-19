---
rg: 2
id: closed-multiplicity-cycle-kills-carrier-trace
kind: claim
title: A closed expanding multiplicity cycle kills its carrier with depth-independent normalized-HS loss
artifacts:
  - research/artifacts/closed-multiplicity-cycle-trace-ledger-2026-08-21.md
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that is one binary Leavitt cell returning to the same projection; this allows different intermediate reservoirs and an arbitrary closed cycle of branching degrees.
  same-orbit-closure: that is the open decoder forcing the source and returned child labels into the same finite reservoir; this is the trace endpoint once that closure has been obtained.
---

Let `P_0,...,P_m` be projections in `M_d(C)`.  At step `e`, let the
branching degree be `r_e >= 1` and let `S_(e,j),T_(e,j)` be arbitrary
matrices, `1 <= j <= r_e`.  Put

```text
epsilon_(e,j) = ||T_(e,j) S_(e,j)-P_e||_2,
sigma_e       = ||sum_j S_(e,j) T_(e,j)-P_(e+1)||_2,
rho           = ||P_m-P_0||_2.
```

Write `R = prod_e r_e` and `R_(>e)=prod_(k=e+1)^(m-1) r_k`.  Then

```text
(R-1) tr(P_0)
 <= rho + sum_(e=0)^(m-1) R_(>e)
                    (sigma_e + sum_j epsilon_(e,j)).       (CMC1)
```

In particular, for a binary cycle (`r_e=2`) in which every displayed
Leavitt defect is at most `epsilon`,

```text
tr(P_0) <= 3 epsilon + rho/(2^m-1).                         (CMC2)
```

Thus recursively closing the same binary multiplicity reservoir does not
cost `m epsilon`: after division by the total expansion, all intermediate
errors form a geometric average and the coefficient remains exactly `3`.
Equivalently, if `tr(P_0) >= c` and `rho=o(1)`, some cell defect is at least
`c/3-o(1)`, independently of depth and matrix dimension.

This does not produce the common reservoir.  It proves that
`same-orbit-closure`, a common-carrier transverse recovery theorem, or a
fixed-scale contextual return is the only load-bearing decoder step left in
the corresponding lanes; error accumulation after closure is not another
obstruction.
