---
rg: 2
id: canonical-left-comb-kl-gate-is-a-mixed-involution
kind: claim
title: The canonical left-comb transport makes the KL gate an explicit mixed involution
distinct_from:
  leavitt-length-six-three-gate-weight-survivor: that uses the gate inside EL20 and never transports it to the unit-group corner; this fixes the canonical prefix equivalence and computes its image.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that gives a necessary mixedness condition; this supplies the first explicit KL-lane conjugator satisfying it.
  leavitt-cylinder-swaps-generate-thompson-in-el: that transports coefficient-one prefix permutations; this transports the two coefficient-bearing far roots of the KL gate.
artifacts:
  - research/artifacts/kl-gate-in-c3-corner-chart-2026-08-21.md
---

For the canonical 20-leaf left-comb code `alpha`, the image in `R^x` of

```text
q=x_34(s_1)x_(11,12)(t_0)
```

is

```text
qhat=(1+s_(alpha_3)s_1t_(alpha_4))
     (1+s_(alpha_11)t_0t_(alpha_12)).
```

The two off-diagonal prefix roots have square zero and annihilate each other,
so `qhat^2=1`.  In the inverse two-leaf chart, the `(1,1)` entry contains the
distinct reduced mixed monomials

```text
t_1(s_(alpha_3)s_1t_(alpha_4))s_1=s_101 t_0t_1t_1
```

and `t_1(s_(alpha_11)t_0t_(alpha_12))s_1`.  Neither can cancel the other or
the scalar entry.  Hence that matrix entry lies in neither coefficient free
subalgebra, and `qhat` lies outside both pure coefficient charts.
