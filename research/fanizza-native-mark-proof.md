---
rg: 2
id: fanizza-native-mark-proof
kind: route
title: Compute the signal involution distance in the membership GNS model and every strategy
target: fanizza-signal-involution-is-native-mark
requires:
  - fanizza-et-al-computable-bcs-signal-family
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
---

If `m` halts, `(FBS1)` supplies a tracial state `tau` with `tau(D_m)>0`.
In its GNS representation with cyclic vector `xi`, the involution relation
gives

```text
||(pi(x_(D,m))-I)xi||^2
 =tau((x_(D,m)-1)^*(x_(D,m)-1))
 =4 tau(D_m)>0.
```

Hence `pi(x_(D,m))!=I`, proving `(NSM1)`.

For any BCS strategy, its Bob observable `X_(D,m)` is a self-adjoint
involution and its associated state satisfies

```text
||X_(D,m)-I||_(2,phi)^2
 =phi((X_(D,m)-I)^*(X_(D,m)-I))
 =2-2phi(X_(D,m))
 =4phi(D_m).                                                     (NSM3)
```

When `m` does not halt, `(FBS2)` bounds the last expression by
`4C_m epsilon`, proving `(NSM2)`.
