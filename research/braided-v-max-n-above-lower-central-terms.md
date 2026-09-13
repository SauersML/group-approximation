---
rg: 2
id: braided-v-max-n-above-lower-central-terms
kind: claim
title: For each c, ascending chains of normal subgroups of bV containing gamma_c(P_br) stabilize
distinct_from:
  every-quotient-of-braided-v-is-finitely-presented: that claim is full max-n for bV; this claim is max-n only among normal subgroups containing a fixed lower central term of the pure braided kernel
---

Let `P_br = ker(V_br -> V)` and fix `c >= 1`. Every ascending chain of normal subgroups
of `V_br` that all contain `gamma_c(P_br)` stabilizes.

Equivalently, `V_br/gamma_c(P_br)` satisfies max-n. Every such normal subgroup is
therefore the normal closure of `gamma_c(P_br)` together with finitely many elements.
Hence every quotient of `V_br` by a normal subgroup containing `gamma_c(P_br)` is
finitely presented if and only if `V_br/gamma_c(P_br)` is. For `c = 1` that quotient is
`V`, which is finitely presented.
