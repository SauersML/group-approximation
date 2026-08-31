---
rg: 2
id: arbitrary-core-near-top-coverage-controls-relative-corner
kind: claim
title: Arbitrary-core near-top coverage controls the relative finite corner
distinct_from:
  relative-induced-selector-has-intertwiner-order-dual: that computes the exact support and distance SDP on the whole induced intertwiner module; this gives a spectral sufficient condition and its smaller coverage dual.
  almost-full-hecke-frame-gives-flexible-corner: that proves the filler estimate for the regular core using a commutant square root; this proves it for every prescribed core representation using the canonical induced isometry.
  near-top-hecke-coverage-has-exact-hole-dual: that gives the regular-core coverage SDP and forced hole certificate; this gives the arbitrary-beta module version.
---

Use the arbitrary-core induced-module notation

```text
rho=Ind_B^G(beta),
D_beta=beta(B)',
E_beta=Hom_B(H_beta,H_rho),
T_X(V)=P_E(rho(x)VX),
```

where `x` and the target `X` are selfadjoint involutions. Let

```text
Q_epsilon=1_[1-epsilon,1](T_X).                        (ACN1)
```

If finitely many `V_j in Q_epsilon E_beta` satisfy

```text
P=sum_j V_j*V_j<=1,       tr_d(1-P)<=delta,            (ACN2)
```

then

```text
Delta_(G,B,beta)(X)<=sqrt(2 epsilon+4 delta).           (ACN3)
```

Define the optimal near-top coverage

```text
c_(epsilon,beta)
 =max {tr_d(P): P=sum_j V_j*V_j<=1,
                   V_j in Q_epsilon E_beta}.           (ACN4)
```

It has the exact hole dual

```text
c_(epsilon,beta)
 =min {tr_d(Z): Z in D_beta, Z>=0,
       Q_epsilon R_Z Q_epsilon>=Q_epsilon}.            (ACN5)
```

Consequently

```text
Delta_(G,B,beta)(X)
 <=sqrt(2 epsilon+4(1-c_(epsilon,beta))).              (ACN6)
```

If instead `Delta_(G,B,beta)(X)>=eta>0` and
`epsilon<=eta^2/4`, an attained dual certificate satisfies

```text
Z>=0,
tr_d(Z)<=1-eta^2/8,
Q_epsilon R_Z Q_epsilon>=Q_epsilon.                   (ACN7)
```

Equivalently, every `V` in the near-top module obeys

```text
tr_d(Z V*V)>=||V||_(2,d)^2.                            (ACN8)
```

Thus the full authenticated Iwahori problem, including nonregular core
types, has the same dichotomy as the regular face. Almost-full near-top
coverage produces the finite Stinespring corner with the allowed
trace-small filler. Any persistent selector gap forces a small-trace
right-module majorant of the entire near-top band.

No known LLP, MF, local-reflexivity, or Fejer--Riesz theorem rules out
the moving certificates (ACN7). The nonhyperlinear-group root remains
open.

DERIVATION
arbitrary-core-near-top-coverage-proof
