---
rg: 2
id: kt-kh-laurent-interface-is-locally-hs-unstable
kind: claim
title: The Kazhdan packet plus mixed return generates the Laurent actor but has no universal local HS correction
distinct_from:
  kt-local-actor-correction-pays-majorana-return: that computes the terminal Majorana floor conditional on a correction modulus; this proves that such a modulus is false for arbitrary Laurent-actor microstates and therefore must use extendability to the full actor and lamp relations.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: that constructs nonexactifiable canonical lamp microstates for one ascending HNN actor; this is an actor-only no-go for the finite K union {h} interface and uses local HS instability of the Laurent elementary group.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is the general local-instability theorem; this identifies the explicit finite generating set to which it applies in the Kun--Thom mixed-return problem.
---

**ESTABLISHED.**  In the `q=2`, `d=3` Kun--Thom system, put

```text
R_0=F_2[x_1,x_2,x_3],       s=x_1x_2x_3,
R=R_0[s^(-1)]=F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)],
Gamma=EL_r(R_0),             E=EL_r(R),
h=e_12(s^(-1)).                                             (KLI1)
```

Let `K` be the elementary Kazhdan packet generating `Gamma`.  Then

```text
<K,h>=E.                                                       (KLI2)
```

Nevertheless there are normalized-HS asymptotic representations of `E`
on increasing finite multiplication windows which stay a fixed positive
distance on `K union {h}` from every genuine same-dimensional
representation of `E`.  Equivalently, there is no universal modulus
`eta(t)->0` with

```text
max_(g in K union {h})||u(g)-rho(g)||_2
 <= eta(def_F(u))                                             (KLI3)
```

for arbitrary `E`-microstates and genuine `rho:E->U(d)`.

Thus the local correction hypothesis in
`kt-local-actor-correction-pays-majorana-return` is genuinely
source-restricted.  A successful robust Majorana floor must consume the
fact that the actor microstate extends across the external `A,B` action and
the lamp/Majorana table.  Property `(T)`, robust adjoint spectral gap, all
Laurent elementary multiplication laws, and finite-dimensional compression
invisibility do not by themselves supply the missing modulus.

DERIVATION
kt-kh-laurent-interface-local-instability-proof
