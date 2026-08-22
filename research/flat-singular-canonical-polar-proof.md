---
rg: 2
id: flat-singular-canonical-polar-proof
kind: route
title: Tensor with a finite regular coefficient of constant generator value
target: canonical-exact-polar-models-have-flat-singular-loss
requires: []
---

Residual finiteness gives a finite quotient `q:A->Q` in which every element
of `S_A` remains nonidentity.  Put `N=|Q|` and let `lambda` be the regular
representation on `ell^2(Q)`.  Write

```text
eta=N^(-1/2) sum_(x in Q) delta_x,
zeta=(delta_e-N^(-1/2)eta)/sqrt(1-1/N).                  (FSL3)
```

Then `eta` is invariant, `zeta` is a unit vector orthogonal to it, and for
every nonidentity `x in Q`,

```text
<lambda(x)zeta,zeta>=-1/(N-1).                           (FSL4)
```

Choose

```text
a=(1+t(N-1))/N,             xi=sqrt(a)eta+sqrt(1-a)zeta.
```

The invariant and orthogonal summands do not mix, so `(FSL4)` gives

```text
<lambda(q(s))xi,xi>=a-(1-a)/(N-1)=t                    (FSL5)
```

for every `s in S_A`.

Choose a chain of finite quotients of the residually finite group `A` which
eventually separates every nonidentity word, and let `rho_n` be their regular
representations.  These are exact and their characters converge pointwise
to the regular character.  Define

```text
pi_n=rho_n tensor lambda,
P_n=1 tensor |xi><xi|.                                   (FSL6)
```

The carrier has fixed ambient trace `1/N`.  Under the natural identification
of its range with the `rho_n` space, `(FSL5)` is exactly `(FSL1)`.  Because
`t>0`, the polar factor of `t rho_n(s)` is uniquely `rho_n(s)`.  Finally

```text
(P_npi_n(s)P_n)^*(P_npi_n(s)P_n)=t^2P_n,
```

and unitarity of `pi_n(s)` gives `(FSL2)`.  Every claimed property is exact
at each finite stage.

