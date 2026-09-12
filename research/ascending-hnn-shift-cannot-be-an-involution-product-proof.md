---
rg: 2
id: ascending-hnn-shift-cannot-be-an-involution-product-proof
kind: route
title: Apply the HNN height character to the reversing involution
target: ascending-hnn-shift-cannot-be-an-involution-product
requires: []
---

Every defining HNN relation has total `t`-exponent zero, so

```text
chi:G -> Z,       chi(t)=1,       chi(H)=0
```

is a homomorphism. If `t=u_1u_2` with `u_i^2=1`, then

```text
u_1 t u_1=u_2u_1=t^(-1).
```

But a homomorphism to an abelian group is constant on conjugacy classes,
whereas `chi(t)=1` and `chi(t^(-1))=-1`. This is impossible.

