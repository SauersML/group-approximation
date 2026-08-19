---
rg: 2
id: low-gap-transport-not-geometric-integralization-proof
kind: route
title: Mix two nearby scalar types by a forty-five-degree unitary
 target: low-gap-transport-not-geometric-integralization
requires: []
---

It is enough to work with the group `H=Z=<g>`.  Let `N->infinity`, choose
`epsilon_N->0`, and on `C^N` let

```text
theta_N(g)=1,
eta_N(g)=exp(i epsilon_N).
```

On `C^(2N)=C^N directSum C^N` define

```text
rho_N=theta_N directSum eta_N
```

and let

```text
W=(1/sqrt(2)) [[I,I],[-I,I]],
sigma_N=W^* rho_N W.
```

Both are exact representations.  Use the identity as the comparison unitary.
Since conjugating the two scalar eigenvalues through the displayed two-by-two
Hadamard rotation only mixes their difference,

```text
||rho_N(g)-sigma_N(g)||_2^2
 = (1/2)|1-exp(i epsilon_N)|^2 -> 0.                 (1)
```

Let `P_0,P_1` be the two coordinate isotypic projections for `rho_N` and put
`Q_j=W^*P_jW`, the isotypic projections for `sigma_N`.  Every diagonal block
of every `Q_j` is `(1/2)I_N`, hence

```text
||P_i Q_j||_2^2 = tr_(2N)(P_iQ_j)=1/4              (2)
```

for all four pairs.  On `P_i M_(2N) Q_j` the two exact representations act by
scalar characters, so the mixed Rayleigh quotient is identically

```text
lambda_(i,j)=|a_i-a_j|^2,
a_0=1, a_1=exp(i epsilon_N).                          (3)
```

Thus the diagonal block energies are zero and the off-diagonal energies tend
to zero.  In particular, for any threshold tending to zero more slowly than
`epsilon_N^2`, the bad transport mass is exactly zero.

What fails is geometric alignment.  For every `i,j`, the two subspaces
`P_i C^(2N)` and `Q_j C^(2N)` meet at constant principal angle `pi/4`:

```text
||Q_j v|| = (1/sqrt(2))||v||       for v in ran(P_i). (4)
```

Suppose a block-respecting matching retains a subspace of total dimension
`r_N` and is a unitary `V_N` on that retained source, with each matched source
summand contained in some `ran(P_i)` and its image contained in some
`ran(Q_j)`.  For every unit vector `v` in a matched source summand, `(4)` gives

```text
Re <v,V_N v> <= |<v,V_N v>| <= 1/sqrt(2),
```

so

```text
||V_Nv-v||^2 >= 2-sqrt(2).                            (5)
```

Summing `(5)` over an orthonormal basis of the retained source yields

```text
||V_N-I||_(2,2N)^2 >= (2-sqrt(2)) r_N/(2N).          (6)
```

Deleting `o(N)` dimensions leaves `r_N/(2N)->1`; adding `o(N)` dimensions
cannot dilute the normalized bound.  Hence the right side of `(6)` tends to
`2-sqrt(2)>0`, contradicting near-identity integralization.

The construction attacks only the inference from low-energy transportation
data to geometric matching.  It deliberately does not satisfy the additional
opposite modular extension constraints of the Iwahori problem, so those
constraints remain exactly the structure a successful completion must use.