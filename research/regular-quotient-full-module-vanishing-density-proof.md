---
rg: 2
id: regular-quotient-full-module-vanishing-density-proof
kind: route
title: Tensor regular quotient blocks with one balanced qubit
target: full-right-edge-module-can-have-vanishing-adjoint-density
requires:
  - commutant-density-trace-blind
---

Choose finite quotients

```text
q_n:Gamma->Q_n
```

whose left regular representations have canonical limiting character.  In
the characteristic-two elementary group fix a nontrivial root involution
`a in Gamma`, and choose the residual chain so that `q_n(a)!=1`.  Put

```text
H_n=ell^2(Q_n) tensor C^2,
rho_n(g)=lambda_(Q_n)(q_n(g)) tensor 1_2,
B_n=C*(lambda_(Q_n)(Q_n)) tensor 1_2.                  (RFM1)
```

Then `d_n=2|Q_n|`, `dim_C(B_n)=|Q_n|`, and `rho_n` has the canonical
`Gamma`-character.  Let

```text
b_n=rho_n(a),                 x_n=1 tensor Z,           (RFM2)
```

where `Z=diag(1,-1)`.  Since nontrivial left translation by the involution
`q_n(a)` is a disjoint union of two-cycles, `b_n` has equal positive and
negative multiplicities.  The same is true of `x_n`, so a unitary `T_n`
exists with

```text
T_n^*b_nT_n=x_n.                                       (RFM3)
```

For every `c in C*(lambda_(Q_n)(Q_n))`,

```text
<x_n,c tensor 1>=tr(c)tr(Z)=0.                         (RFM4)
```

Therefore `E_(B_n)(x_n)=0`.  Since `x_n` is unitary, left multiplication by
`x_n` identifies `B_n` with `x_nB_n`; this proves `(FMD2)--(FMD3)`.  Finally

```text
dim_C(x_nB_n)/d_n^2
 =|Q_n|/(4|Q_n|^2)=1/(4|Q_n|)->0,                      (RFM5)
```

which proves `(FMD4)`.
