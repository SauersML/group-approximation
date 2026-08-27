---
rg: 2
id: approximate-schur-replicas-force-exponential-dimension-proof
kind: route
title: Flexibly exactify the whole replica table and apply the exact dimension bound
target: approximate-schur-replicas-force-exponential-dimension
requires:
  - gowers-hatami-finite-group-hs-stability
  - commuting-schur-replicas-force-exponential-dimension
---

Apply `(GHS2)` to obtain `rho:K_N->U(m)` with
`m<=d/(1-4epsilon^2)`.  Each signed forbidden element `Q_i^-` is a fixed
linear combination of a bounded number of packet group elements.  Applying
`(GHS2)` term by term to that Fourier
polynomial gives

```text
Re tau_d(V^*Q_i^-(rho)V) >= b-K_B epsilon.
```

Since `Q_i^-(rho)` is the actual projection onto the forbidden selector
sectors on which `rho(J)=-I`,

```text
tau_m(Q_i^-(rho))
 >= (d/m)(b-K_B epsilon)
 >= b_epsilon.                                                   (ASE4)
```

The selected packet factors commute across sites.  Repeat the joint spectral
counting proof of `commuting-schur-replicas-force-exponential-dimension` using
`(ASE4)`: a nonzero exact joint sector is forbidden at at least
`ceil(b_epsilon N)` sites, so projective holonomy gives

```text
m >= 2^(ceil(b_epsilon N)).
```

Combine this with the upper bound on `m` and rearrange to obtain `(ASE2)`.
Condition `(ASE3)` contradicts `(ASE2)`.
