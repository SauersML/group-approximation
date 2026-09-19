---
rg: 2
id: context-local-leakage-countermodel-proof
kind: route
title: Reduce global leakage to mixed energy and separate it from local bridge energy
target: context-local-fanizza-exits-do-not-control-global-leakage
requires: []
---

Let `L_i=(1-C)E_i`.  For every shared involution `Z_x`,

```text
[L_i,Z_x]=(1-C)[E_i,Z_x]-[C,Z_x]E_i.
```

For each fixed BCS residual polynomial `R`, similarly

```text
R(Z)L_i=(1-C)R(Z)E_i-[R(Z),C]E_i.
```

Squared triangle inequalities and fixed-length commutator telescoping give
a dimension-independent constant `K_B` such that the complete leakage
functional is at most `K_B` times

```text
sum_x||[C,Z_x]||_2^2
+sum_(i,x)||(1-C)[E_i,Z_x]||_2^2
+sum_(i,R)||(1-C)R(Z)E_i||_2^2.
```

This proves the exact sufficient mixed row.

It cannot follow from context-local bridges.  Before adding a mixed
two-cell, those packets form a finite graph of finite groups.  At a leaf
vertex choose a nonzero private leakage projection `L` outside the edge
group algebra and a shared variable word `Y` in another vertex.  In the
Bass--Serre regular representation, reduced normal forms show `[L,Y]!=0`.
The graph group is virtually free and residually finite, so finite quotients
separating the finite support of this commutator give exact finite-dimensional
models with zero local relator energy and

```text
liminf ||[L_n,Y_n]||_2>0.
```

Hence no local-energy inequality can control global leakage; the mixed row
is genuinely additional.
