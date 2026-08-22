---
rg: 2
id: sofic-dyadic-coset-action-makes-hnn-sofic-proof
kind: route
title: Apply free generalized wreath-product permanence to the dyadic orbit
target: sofic-dyadic-coset-action-makes-hnn-sofic
requires:
  - sl2-centralizer-hnn-is-free-coset-wreath
---

Assume `A curvearrowright A/C` is sofic.  The linear group
`A=SL_2(Z[1/2])` is residually finite, hence sofic, and the lamp group `Z`
is amenable, hence sofic.  By
`sl2-centralizer-hnn-is-free-coset-wreath`, the HNN group is

```text
Z wr^*_(A curvearrowright A/C) A.
```

Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group actions on sets
and applications*, Research in the Mathematical Sciences 12 (2025), 48,
Theorem 3.7, says that this free generalized wreath product is sofic.  Sofic
groups are hyperlinear, proving the conditional claim.
