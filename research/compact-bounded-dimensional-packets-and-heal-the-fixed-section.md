---
rg: 2
id: compact-bounded-dimensional-packets-and-heal-the-fixed-section
kind: route
title: Compact bounded-dimensional representation varieties and heal the fixed section
target: fixed-section-positive-packet-gaps-escape-bounded-dimension
requires:
  - fd-representation-packets-never-obstruct-ucp-sections
---

We first prove `(FSG3)`.  Suppose it fails.  After passing to a subsequence
there are `epsilon>0`, integers `m_k->infinity`, one fixed `d<=D`, and unital
representations

```text
rho_k:A->M_d
```

such that

```text
dist(rho_k o (t+v),UCP(E,M_d))>=epsilon
                         for every v in V_(m_k).           (1)
```

The space of unital representations `A->M_d` is compact in the topology of
pointwise norm convergence: each closed norm ball in `M_d` is compact, and
the unital, linear, star-preserving and multiplicative equations are closed
in the corresponding product.  Pass to a subnet, still denoted `rho_k`,
which converges pointwise to a representation `rho:A->M_d`.

Apply `fd-representation-packets-never-obstruct-ucp-sections` to the singleton
packet `{rho}`.  There is a unital self-adjoint section

```text
s:E->A,       q s=id_E,       rho o s in UCP(E,M_d).       (2)
```

Put `h=s-t`.  Then `h:E->I` is self-adjoint and `h(1)=0`.  Since `E` is
finite-dimensional and the `L_m` exhaust `I`, choose

```text
v_k in V_(m_k),       ||v_k-h||->0.                        (3)
```

Pointwise convergence of `rho_k` to `rho` is uniform on the fixed
finite-dimensional range `s(E)`.  Contractivity of every representation and
`(3)` therefore give

```text
||rho_k o (t+v_k)-rho o s||
 <=||v_k-h||+||(rho_k-rho)o s|| ->0.                       (4)
```

The second map in `(4)` is ucp by `(2)`, contradicting `(1)`.  This proves
uniform convergence over each bounded matrix dimension.  The argument uses
only compactness of `M_d` and the one-packet section theorem; RFD of `A` and
any information about `rho(I)` are absent.

For `(FSG6)`, apply the same compactness argument to the sequence `rho_m`.
It supplies maps `v_m in V_m` and one limiting-packet section `s` such that,
along every subsequence on which the dimensions are fixed,

```text
||rho_m o(t+v_m)-rho_m o s||->0.                           (5)
```

Central compression of a ucp map is cp, so

```text
theta_m=z_m rho_m o s in UCP_(z_m)(E,J_m).                (6)
```

Use reservoir annihilation and `(6)` in `(FSG5)`:

```text
gamma_m(t)
 =Omega_m(z_m rho_m o(t+v_m))-sup_theta Omega_m(theta)
 <=Omega_m(z_m rho_m o(t+v_m-s))
 <=C ||rho_m o(t+v_m-s)|| ->0.                            (7)
```

There are only finitely many possible dimensions below `D`, so `(7)` on
every fixed-dimension subsequence proves `(FSG6)`.  Positivity of `Omega_m`
is not used after its dimension-free norm bound has been obtained.

Finally let `t'` be a second fixed section and put `a=t-t':E->I`.  Choose
`a_m in V_m` with `||a_m-a||->0`.  The relative-unital Choi slice in
`(FSG5)` is independent of the chosen raw section, while `(FSG4)` kills
`a_m`; hence

```text
|gamma_m(t)-gamma_m(t')|
 =|Omega_m(z_m rho_m o a)|
 =|Omega_m(z_m rho_m o(a-a_m))|
 <=C||a-a_m|| ->0.                                       (8)
```

This proves `(FSG8)` in arbitrary moving dimensions and completes the route.
