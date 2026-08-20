---
rg: 2
id: ascending-hnn-shift-cannot-be-an-involution-product
kind: claim
title: A strict ascending-HNN shift cannot be identified with a product of two involutions
---

Let

```text
G=<H,t | t h t^(-1)=sigma(h), h in H>
```

be an ascending HNN extension. Its height homomorphism sends `t` to `1` and
`H` to `0`. If a quotient preserving this height and the embedded HNN
skeleton imposed

```text
t=u_1 u_2,       u_1^2=u_2^2=1,
```

then `u_1 t u_1=t^(-1)`. Conjugacy invariance of height would give `1=-1`.
Equivalently, applying height directly to `t=u_1u_2` gives `1=0`, since every
torsion element maps to zero in `Z`.

Thus the Toeplitz ascending shift cannot literally be the Fanizza word
`U=U_1U_2` while retaining the strict ascending-HNN height structure. A
viable compiler must keep the shifts distinct and synchronize their
conjugation actions instead.

