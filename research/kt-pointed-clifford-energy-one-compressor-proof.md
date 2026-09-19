---
rg: 2
id: kt-pointed-clifford-energy-one-compressor-proof
kind: route
title: Read the Majorana second moment in the sofic one-compressor wreath
target: kt-pointed-clifford-energy-one-compressor-no-go
requires:
  - kt-single-compressor-canonical-lamps-do-not-exactify-actor
---

In `M_Cl=Cl(G/Gamma) crossed_product G`, the stabilizer of the site
`t Gamma` under `Gamma` is

```text
Gamma cap t Gamma t^(-1)=Lambda.
```

Hence `x_Cl=c_(t Gamma)` commutes with `u(Lambda)`.  Since
`gamma_0 notin Lambda`, the sites `t Gamma` and `gamma_0 t Gamma` are
distinct.  Distinct Majoranas are orthogonal in `L^2(Cl(G/Gamma))`, so

```text
tau(x_Cl u_(gamma_0)x_Clu_(gamma_0)^*)=0.
```

As both terms are unitaries,

```text
||[x_Cl,u_(gamma_0)]||_2^2
 =||x_Cl-u_(gamma_0)x_Clu_(gamma_0)^*||_2^2=2.
```

For the matrix models, use the one-compressor generalized wreath

```text
W_t=(direct_sum_(V/Gamma) C_2) semidirect V.
```

By `kt-single-compressor-canonical-lamps-do-not-exactify-actor`, `W_t` is
sofic and has canonical permutation microstates `phi_n`.  Let

```text
rho_n=phi_n restricted_to V,
X_n=phi_n(a_(t Gamma)).
```

Every assertion in the first two lines of `(PCE2)` is a fixed group-word or
trace condition in `W_t`: `a_(t Gamma)` is a nontrivial involution, its
stabilizer contains `Lambda`, and canonical microstates have trace zero on
nontrivial words.  Therefore those defects tend to zero, as do all fixed
actor multiplication defects.

The conjugate lamp `a_(gamma_0 t Gamma)` is distinct from `a_(t Gamma)`.
Their product is a nontrivial element of the binary lamp base, hence has
canonical trace zero.  Consequently

```text
||[X_n,rho_n(gamma_0)]||_2^2
 =2-2 Re tr(X_n rho_n(gamma_0)X_n rho_n(gamma_0)^*) ->2.
```

If the asserted modulus existed, its right-hand side would tend to zero on
this sequence while its left-hand side tends to two, a contradiction.

The Clifford and binary pairs differ at the next operator moment: distinct
Majoranas anticommute, whereas distinct binary lamps commute.  Their scalar
overlap `tau(xy)=0`, trace-zero involution laws, stabilizer laws and pointed
commutator energy are identical.  This proves exactly the stated scope and
does not furnish a countermodel once anticommutation or the full actor is
required.
