---
rg: 2
id: torsion-free-nonrf-from-torsion-free-residual
kind: route
title: Pass to a torsion-free finite-index subgroup of a counterexample with torsion-free residual
target: torsion-free-non-residually-finite-hyperbolic-group
requires:
  - nonrf-hyperbolic-group-with-torsion-free-residual
  - finite-torsion-carrier-virtual-torsionfree-criterion
  - finite-residual-transports-across-commensurability
---

Let `G` be word-hyperbolic with `R_f(G) != 1` torsion-free.  Hyperbolic groups
have finitely many conjugacy classes of finite subgroups, so the torsion-carrier
criterion gives a torsion-free normal subgroup `L` of finite index.

`L` is word-hyperbolic (finite index).  Every finite-index subgroup contains
`R_f(G)`, so `R_f(G) <= L`, and finite-index heredity gives

```text
R_f(L) = R_f(G) ∩ L = R_f(G) != 1.
```

So `L` is torsion-free, hyperbolic and not residually finite.  With
`torsion-free-residual-from-torsion-free-nonrf` this forms an intended
equivalence cycle.
