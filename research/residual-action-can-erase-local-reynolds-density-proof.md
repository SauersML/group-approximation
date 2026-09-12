---
rg: 2
id: residual-action-can-erase-local-reynolds-density-proof
kind: route
title: Tensor both packet algebras with a full residual matrix algebra
target: residual-action-can-erase-local-reynolds-density
requires: []
---

Put `A=Alg(H)<=C=Alg(B)<=End(K)`. Before adjoining the residual action,

```text
(A tensor I_m)'=A' tensor M_m,
(C tensor I_m)'=C' tensor M_m,
```

so the difference of commutants has dimension

```text
(dim A'-dim C')m^2.                                           (1)
```

After the same full residual algebra is adjoined to both sides as in
`(REA1)`,

```text
(A tensor M_m)'=A' tensor C I_m,
(C tensor M_m)'=C' tensor C I_m.                              (2)
```

The difference now has fixed dimension `dim A'-dim C'`. Its normalized
adjoint density is

```text
(dim A'-dim C')/(dim(K)^2 m^2),                               (3)
```

which tends to zero. This calculation uses exact finite-dimensional
algebras, so no perturbative qualification can repair the missing hypothesis.

