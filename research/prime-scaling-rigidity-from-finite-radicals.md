---
rg: 2
id: prime-scaling-rigidity-from-finite-radicals
kind: route
title: Recover the prime from the finite radical of a maximal Kazhdan subgroup
target: prime-scaling-subfamily-pairwise-nonisomorphic
requires:
  - prime-scaling-maximal-kazhdan-blocks
---

An isomorphism `E_p -> E_q` preserves property `(T)), subgroup inclusion,
and maximality.  It therefore sends a maximal property-`(T)` subgroup of
`E_p` onto a maximal property-`(T)` subgroup of `E_q`.

The unique largest finite normal subgroup of an abstract group is
characteristic.  By the prerequisite, its orders on these two maximal
Kazhdan subgroups are respectively

```text
2^(p^3+1)  and  2^(q^3+1).
```

They must be equal, so `p^3=q^3` and hence `p=q`.  Thus different primes
give non-isomorphic scaling groups.
