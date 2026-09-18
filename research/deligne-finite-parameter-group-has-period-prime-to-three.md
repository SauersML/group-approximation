---
rg: 2
id: deligne-finite-parameter-group-has-period-prime-to-three
kind: claim
title: If Deligne's norm-parameter group is finite then its order is prime to three
distinct_from:
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that asserts 1/3 is not in P_op outright; this asserts it only on the finite branch, so it says nothing when P_op = R/Z and is strictly weaker.
  deligne-sep7-norm-parameter-closed-subgroup: that proves P_op is R/Z or (1/m)Z/Z with m even; this asks for the residue of m at the prime three on the finite branch.
  sp4-quasirep-windings-are-sublinear: that would exclude the branch P_op = R/Z; this is about the complementary finite branch and is independent of windings.
---

**OPEN.** Let `P_op` be the norm-parameter group of `deligne-sep7-norm-parameter-closed-subgroup`. The claim is:

```text
if P_op = (1/m)Z/Z for some even m, then 3 does not divide m.
```

Equivalently, `1/3 in P_op` implies `P_op = R/Z`. In words: an operator-norm `1/3`-model of the Maslov cocycle
already forces arbitrarily small parameters.

**Why it matters.** Together with `sp4-quasirep-windings-are-sublinear`, it gives the flagship
`deligne-triple-cover-exact-mf-radical`, through route `deligne-triple-cover-via-sublinear-windings`. It is the
arithmetic half of that split, and it involves no winding estimate.

**How it can fail.** An MF model of `E_3` (a `1/3`-model) whose parameter group is still finite, for example
`P_op = (1/6)Z/Z`. Such a model would make `E_6` MF while `E_q` is not MF for every `q` not dividing `6`.

## Attempts
- **2026-09-18, swarm-0917-w7-w7-deligne-break: posed.** No test has been run. The tensor-power amplification of
  `deligne-sep8-first-order-tensor-threshold` needs `o(|t|)` errors with `t -> 0`. It does not start from one fixed
  parameter `1/3` with nonzero error, so it gives no leverage here.
