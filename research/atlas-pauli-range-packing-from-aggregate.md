---
rg: 2
id: atlas-pauli-range-packing-from-aggregate
kind: route
title: Aggregate almost-projections supply every range-packing error
target: atlas-pauli-range-packing-recurrence
requires:
  - atlas-pauli-aggregate-range-recurrence
  - aggregate-range-idempotence-replaces-gram-bookkeeping
---

Take the fixed automaton from `atlas-pauli-aggregate-range-recurrence` and fix
a target `j`.  Write `F_e=T_eT_e^*` for each incoming branch and
`F_j=sum_e F_e`.

For each edge, the leakage trace is nonnegative and

```text
sum_(e->j) tau((1-P_j)F_e)
 = tau((1-P_j)F_j)
 = O(delta^c).
```

Since the number of incoming edges is fixed and every summand is nonnegative,
each individual term is `O(delta^c)`.  This is `(RPR1)`.

The aggregate-range theorem gives the exact identity

```text
sum_(e!=f -> j) tau(F_eF_f)
 = tau(F_j^2-F_j)
```

and hence the bound

```text
sum_(e!=f -> j) tau(F_eF_f)
 <= ||F_j^2-F_j||_2
 = O(delta^c).
```

This is `(RPR2)`.  Strong connectivity, exact source projections, the fixed
state/word menu, and the exact Pauli split are unchanged.  Therefore every
clause of `atlas-pauli-range-packing-recurrence` follows.
