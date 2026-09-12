---
rg: 2
id: stw99-xcix-z-stable-hull-construction-proof
kind: route
title: Iterate commuting copies into a central sequence of one separable hull
target: stw99-xcix-separable-subalgebras-have-z-stable-hulls
requires:
  - stw99-xcix-zero-distance-z-saturated-limit
---

Adjoin the unit of `P` to `S` and call the resulting separable algebra
`S_0`.  Inductively, Z-saturation supplies a unital embedding

```text
theta_n:Z -> P intersect S_n',
```

and set

```text
S_(n+1)=C*(S_n,theta_n(Z)).
```

Each `S_n` is separable.  Therefore

```text
T=closure(union_n S_n)
```

is a separable unital C*-subalgebra of `P` containing `S`, and every
`theta_n` has range in `T`.

The sequence `(theta_n)` is point-norm central in `T`.  Indeed, if
`x in S_m`, then `S_m subset S_n` and hence

```text
[theta_n(z),x]=0                         (n>=m,z in Z).
```

Density of the increasing union and the commutator Lipschitz bound extend
this convergence to every `x in T`.  Consequently the coordinatewise map

```text
Theta:Z -> T_infinity intersect T',
Theta(z)=[(theta_n(z))_n],
```

is a unital embedding.  The central-sequence characterization of absorption
by the strongly self-absorbing Jiang--Su algebra now gives

```text
T tensor Z isomorphic to T.
```

Thus `T` is the required Z-stable hull.  The argument proves tensorial
absorption only for the constructed separable `T`; no absorption theorem for
the nonseparable ambient ultraproduct is invoked.
