---
rg: 2
id: two-shared-gauge-selector-rank-proof
kind: route
title: Count the two sign sectors and compare spectral projections
target: two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
requires: []
---

Let `G_+=(1+V)/2` and `G_-=(1-V)/2`.  On `H tensor G_+`, the negative
projection of `C_q tensor V` is `F_q tensor G_+`.  On
`H tensor G_-`, multiplication by the negative sign swaps the two spectral
projections, so the negative projection is `(1-F_q) tensor G_-`.  Dividing

```text
q n rank(G_+)+(1-q)n rank(G_-)
```

by `nm` proves `(TSG1)`.  Unitary conjugacy preserves the rank of the
negative spectral projection, proving `(TSG2)`.  Substitution gives

```text
1/2=3/4-theta/2,        hence theta=1/2,
1/4=7/8-3theta/4,       hence theta=5/6.
```

For the robust form, if `P=(1-R_i)/2` and
`Q=(1-T_i)/2`, then

```text
||W_i P W_i^*-Q||_2
  =(1/2)||W_i R_i W_i^*-T_i||_2.
```

Cauchy--Schwarz for the normalized trace gives
`|tau(P)-tau(Q)|<=||W_iPW_i^*-Q||_2`.  Since
`tau(Q)=Phi_(q_i)(theta)`, this is `(TSG3)`.

For `(r_1,q_1)=(1/2,1/4)`, `(TSG3)` rearranges to
`delta_1>=|theta-1/2|`.  For `(r_2,q_2)=(1/4,1/8)`, it rearranges to
`delta_2>=(3/2)|theta-5/6|`.  The weighted triangle inequality gives

```text
delta_1+delta_2
 >= |theta-1/2|+|theta-5/6| >=1/3.
```

For the squared bound, the minimum of

```text
x^2+(9/4)(1/3-x)^2
```

occurs at `x=3/13` and equals `13/169`.  This proves `(TSG4)`.
