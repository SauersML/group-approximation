---
rg: 2
id: trace-separation-sphere-distance-concentration
kind: claim
title: Trace separation gives dimension-improving concentration of spherical word distance
---

Let `U,V in U(d)` and let `x` be uniform on the unit sphere of `C^d`.  With
normalized trace `tau=Tr/d`, put

```text
Z(x) = ||Ux-Vx||^2.
```

Then

```text
E Z = 2 - 2 Re tau(U^* V),
Var(Z) <= 4 (1-|tau(U^*V)|^2)/(d+1) <= 4/(d+1).
```

More precisely, for `D=U^*V`,

```text
E |<x,Dx>-tau(D)|^2 = (1-|tau(D)|^2)/(d+1).
```

Hence for every `a>0`,

```text
Pr[ |Z-(2-2 Re tau(U^*V))| >= a ] <= 4/((d+1)a^2).
```

For a finite trace-separated unitary table, a union bound gives simultaneous
anti-collision for every tested pair of distinct words on a `1-o_d(1)` set of
sphere points.  Thus the mean-to-concentration subgate in
`spherical-candidate-hypergraph-quasirandom` is closed: the remaining work is
the cap-intersection/codegree estimate and the simultaneous design selection,
not concentration of `||U_w x-U_w' x||` for a fixed microstate table.
