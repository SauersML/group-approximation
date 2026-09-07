---
rg: 2
id: leavitt-unit-max-mf-quotient-is-power-cokernel
kind: claim
title: The maximal MF quotient of a Leavitt unit group is the field modulo n minus one powers
distinct_from:
  binary-leavitt-all-ranks-full-mf-radical: that is the total collapse for the binary algebra over any field, and is the case where this computation returns the trivial group; this computes the surviving quotient for every Leavitt algebra L_k(1,n) and exhibits nontrivial values.
  purely-infinite-unit-group-max-mf-quotient-is-k1: that is the general classification; this is its computation for one family, where the answer is explicit.
  leavitt-algebras-over-countable-fields-full-mf-radical: that gives full MF radical for the elementary groups from rank four, which is the commutator part; this computes the abelian part that survives on the whole unit group.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

Let `k` be a countable field and `n >= 2`, and let `R = L_k(1,n)` be the
Leavitt algebra, the rose with `n` petals in the sense of the manuscript's
presentation `t_i s_j = delta_(ij)`, `sum_i s_i t_i = 1`.  Then

```text
K_1(R) = k^x / (k^x)^(n-1),
```

so this is the maximal MF quotient of `R^x`:

| ring | maximal MF quotient of the unit group |
| --- | --- |
| `L_k(1,2)` | trivial |
| `L_(F_2)(1,n)` | trivial |
| `L_(F_q)(1,n)` | `C_(gcd(q-1,n-1))` |
| `L_Q(1,3)` | `Q^x/(Q^x)^2` |

So every MF image of `L_(F_5)(1,3)^x` factors through `C_2`, and that
quotient is attained.  The collapse of the binary case is not automatic; it
is the vanishing of one computable invariant.
