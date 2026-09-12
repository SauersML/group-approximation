---
rg: 2
id: steinberg-tree-cuts-are-five-marginals
kind: claim
title: Every exceptional Steinberg chord cut is one of five explicit marginals
artifacts:
  - research/steinberg-tree-cut-marginal-proof.md
distinct_from:
  steinberg-fox-chord-actions-are-explicit: that gives the generic rational chord maps and leaves exceptional values as signed tree cuts; this evaluates every such cut by five named marginals.
---

**ESTABLISHED.**  For `f:F_p^3 -> F_p`, put

```text
P(a,b)=sum_c f(a,b,c),
H(c,d)=sum_x f(x,xc-d,c),
A(a)=sum_b P(a,b),
C(c)=sum_d H(c,d),
T=sum_(a,b,c) f(a,b,c).                              (STM1)
```

Under the inverse chord extension `E_p`, the five possible tree-edge
coefficients are respectively

```text
-P(a,b),  -H(c,d),  C(c),  A(a),  -T.               (STM2)
```

They occur on the outer-point leaves, outer-plane leaves, `H_0` arms, `z`
arms, and the central edge.  Thus every zero-denominator value in `(SCA2)`
is predetermined by `(STM1)`; there is no additional boundary variable.

DERIVATION
steinberg-tree-cut-marginal-proof
