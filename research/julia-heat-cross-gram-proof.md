---
rg: 2
id: julia-heat-cross-gram-proof
kind: route
title: Compress the Julia unitary between the upper block projection
target: julia-dilation-packages-heat-as-one-cross-gram-moment
requires:
  - fanizza-heat-return-is-one-cyclic-amplitude-product
---

Functional calculus gives `B f(B^*B)=f(BB^*)B`, and in particular
`B D_B=D_(B*)B`.  Multiplying the two block matrices verifies
`U_B^*U_B=U_BU_B^*=1`.  Since `Q_B=U_B^*EU_B`, it is a projection unitarily
equivalent to `E`.  Direct block multiplication gives

```text
E U_B^* E U_B E=diag(B^*B,0),
```

which is `(JHG2)`.  Apply the Chebyshev bound from
`fanizza-heat-filter-has-uniform-cstar-decay` and remember that normalized
`2 by 2` matrix trace contributes the factor `1/2` to obtain `(JHG3)`.
