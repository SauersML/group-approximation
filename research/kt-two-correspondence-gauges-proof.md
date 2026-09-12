---
rg: 2
id: kt-two-correspondence-gauges-proof
kind: route
title: Put a trace-zero spectator sign on return and compressor transports
target: kt-return-compressor-gauges-separate
requires:
  - finite-quotient-blindness
  - commutant-density-trace-blind
---

Choose residual finite quotients

```text
pi_n:G->Q_n
```

whose regular characters converge to the canonical character and in which
`pi_n(a)!=1`.  Put

```text
H_n=ell^2(Q_n) tensor C^2,
rho_n(g)=lambda_(Q_n)(pi_n(g)) tensor 1_2,
B_n=C*(lambda_(Q_n)(pi_n(Gamma))) tensor 1_2.          (TGP1)
```

Let `Z=diag(1,-1)`.

For the return gauge put `u_n=1 tensor Z`.  The involutions `rho_n(a)` and
`u_n` have equal positive and negative multiplicities: nontrivial left
translation by the order-two element `pi_n(a)` is a disjoint union of
two-cycles.  Hence a unitary `S_n` satisfying `(SCG1)` exists.  The tensor
factor shows directly that `u_n` commutes with `B_n` and is orthogonal to it.

For the compressor gauge put

```text
z_n=lambda_(Q_n)(pi_n(t)) tensor Z.                    (TGP2)
```

Finite quotient blindness gives

```text
pi_n(t Gamma t^(-1))=pi_n(Gamma),                      (TGP3)
```

so `theta_n=Ad(rho_n(t))` is an automorphism of `B_n`.  Equation `(TGP2)`
then gives `z_n b=theta_n(b)z_n`.  The trace-zero tensor factor makes `z_n`
orthogonal to `B_n` regardless of the first tensor factor.

Because `u_n` and `z_n` are unitaries and obey their displayed left-action
relations, `(SCG3)` follows and both module dimensions are one.  If
`H_n^Gamma=pi_n(Gamma)` denotes the finite subgroup image, then

```text
dim_C(B_n)=|H_n^Gamma|,
d_n=2|Q_n|,
dim_C(u_nB_n)/d_n^2
 =dim_C(z_nB_n)/d_n^2
 =|H_n^Gamma|/(4|Q_n|^2)
 <=1/(4|Q_n|)->0.                                     (TGP4)
```

This proves every assertion.
