---
rg: 2
id: haar-random-basis-depolarization-proof
kind: route
title: Haar two-design averaging gives the exact random-basis composition formula
target: haar-random-basis-depolarization
requires: []
---

For unit vectors `a,b` and a Haar-random orthonormal basis `{y_j}`, the
second-design identity gives

```text
E sum_j |<a,y_j>|^2 |<y_j,b>|^2
 = (1+|<a,b>|^2)/(d+1).
```

For fixed output `k` and input `i`,

```text
(P_C P_A)_{ki}
 = sum_j |<c_k,V y_j>|^2 |<y_j,U b_i>|^2.
```

Apply the identity with `a=V* c_k`, `b=U b_i`. Their inner product is
`<c_k,VU b_i>=D_{ki}`, so

```text
E(P_C P_A)_{ki} = (1+|D_{ki}|^2)/(d+1).
```

Entrywise this is `(J+P_D)/(d+1)`.
