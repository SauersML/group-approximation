---
rg: 2
id: same-side-modular-hadamard-obstruction-proof
kind: route
title: Hadamard-mix two nearby irreducible modular restrictions
target: same-side-modular-extensions-do-not-integralize-edge-transport
requires: []
---

Write `PSL_2(Z)=<a,b | a^2=b^3=1>`, put

```text
A=diag(1,-1),
D=diag(1,omega),               omega=exp(2 pi i/3),
B_t=W_t D W_t^*,
W_t=[[cos(t),-sin(t)],[sin(t),cos(t)]],
pi_t(a)=A,                     pi_t(b)=B_t.            (1)
```

These are exact two-dimensional modular representations.  For the standard
Iwahori generators

```text
u=ab,                 e=ab^2aba,
```

a direct two-by-two calculation at `t_0=pi/6` gives

```text
det([pi_(t_0)(u),pi_(t_0)(e)]_add)=(27/16)omega !=0,  (2)
```

where `[X,Y]_add=XY-YX`.  Hence the restriction `theta_t=pi_t|B` is
irreducible on a neighborhood of `t_0`.  Moreover

```text
tr(theta_t(u))=(1-omega)cos(2t),                      (3)
```

whose derivative at `t_0` is nonzero.  Thus `theta_(t_0)` and
`theta_(t_0+epsilon)` are inequivalent for all sufficiently small nonzero
`epsilon`, while their generator matrices are `O(epsilon)`-close.

Choose `epsilon_N->0` and set, on
`(C^2 tensor C^N) directSum (C^2 tensor C^N)`,

```text
rho_N=(theta_(t_0) tensor I_N) directSum
      (theta_(t_0+epsilon_N) tensor I_N),
H=(1/sqrt(2))[[I,I],[-I,I]],
sigma_N=H^* rho_N H.                                  (4)
```

Both `rho_N` and `sigma_N` extend to exact modular representations by using
the same formulas with `pi_t`; their identity-comparison edge defect is
`O(epsilon_N)`.  If `P_0,P_1` are the two `rho_N` isotypic projections and
`Q_j=H^*P_jH`, then

```text
tr(P_iQ_j)=1/4                                       (5)
```

for all four pairs.  Diagonal mixed energies are zero and off-diagonal ones
are `O(epsilon_N^2)`, because the two irreducible types are generatorwise
`O(epsilon_N)`-close.

Every `ran(P_i)` meets every `ran(Q_j)` at principal angle `pi/4`.  Therefore
for a block-respecting unitary `V` and every unit vector in its retained
source,

```text
Re <v,Vv> <=1/sqrt(2),
||Vv-v||^2 >=2-sqrt(2).                               (6)
```

Summing over a retained subspace of relative dimension `1-o(1)` proves
`(SME1)`.  Deleting or adding `o(N)` dimensions cannot dilute the bound.
