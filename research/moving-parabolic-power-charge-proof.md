---
rg: 2
id: moving-parabolic-power-charge-proof
kind: route
title: Tensor nearby modular angles with a separating finite-quotient regular tower
target: regular-iwahori-edge-types-have-moving-power-charge
requires:
  - iwahori-edge-restriction-image-has-continuous-type
  - residual-finite-tensor-camouflages-iwahori-transfer-failures
---

There is first a structural obstruction to applying the virtually-free
theorem unchanged.  With rational group Euler characteristic,

```text
chi(V)=chi(C_2*C_3)=-1/6,
chi(H)=chi(Z*C_2)=-1/2,
chi(V *_H V)=2 chi(V)-chi(H)=1/6.                      (MPC0)
```

The amalgam `V *_H V=PSL_2(Z[1/2])` is infinite.  An infinite virtually
free group has Euler characteristic at most zero (pass to a finite-index
free subgroup), so this amalgam cannot be refined to a finite graph of
finite groups.  The finite-edge Gerasimova--Shchepin theorem therefore does
not apply by Bass--Serre subdivision.

Use the two-dimensional family from
`iwahori-continuous-restriction-family-proof`.  Reparameterize it by
`phi in (0,pi/3)` so that

```text
Spec(rho_phi(t))={exp(i phi),-exp(-i phi)}.             (MPC1)
```

This is possible because

```text
Tr(rho_theta(t))=i sqrt(3) cos(2 theta)=2i sin(phi),
```

and the change of variables is bi-Lipschitz on every compact subinterval.
Consequently

```text
(1/2)Tr(rho_phi(t)^m)
 = cos(m phi)                 (m even),
 = i sin(m phi)               (m odd).                (MPC2)
```

Choose a nested separating family of finite quotients

```text
q_n:V -> Q_n
```

and let `m_n` be the order of `q_n(t)`.  Since `t` has infinite order and
the kernels decrease to one, `m_n->infinity`.  For all large `n`, choose
`phi_n,psi_n` in one fixed compact subinterval of `(0,pi/3)` with

```text
psi_n-phi_n=pi/m_n                                   (MPC3)
```

and so that the two values in `(MPC2)` differ by absolute value `2`.
For even `m_n`, choose `m_n phi_n` congruent to `0` modulo `2pi`; for odd
`m_n`, choose it congruent to `pi/2` modulo `2pi`.  The grid spacing is
`2pi/m_n`, so such choices exist in the fixed interval for large `n`.

Let `lambda_n` be the left regular representation of `Q_n` and put

```text
sigma_n=rho_(phi_n) tensor (lambda_n o q_n),
tau_n  =rho_(psi_n) tensor (lambda_n o q_n).           (MPC4)
```

For every fixed `g!=e`, eventually `q_n(g)!=e`, so the regular tensor factor
has trace zero.  This proves regular-character convergence on `V` and on
`H`.  The matrices `rho_phi(x)` are fixed, while `rho_phi(a)` depends
Lipschitzly on `phi` in the chosen compact interval.  Tensoring by a unitary
preserves normalized HS norm; bounded-word telescoping for the fixed edge
generators `t,w` therefore gives `(RPC3)`.

On the moving kernel word `t^(m_n)`, the quotient factor is the identity.
Equations `(MPC2)--(MPC3)` give

```text
|tr_(D_n)(sigma_n(t^(m_n)))
 -tr_(D_n)(tau_n(t^(m_n)))|=2.                        (MPC5)
```

Suppose `(RPC5)` held.  Equality of the stabilized characters at
`t^(m_n)` would make the left side of `(MPC5)` at most

```text
(dim eta_n+dim zeta_n)/D_n,                           (MPC6)
```

because the absolute character of a representation is bounded by its
dimension.  This tends to zero by `(RPC4)`, contradicting `(MPC5)`.

The detector necessarily moves with the quotient: every fixed word has
regular limiting trace.  This is precisely why scalar regularity misses the
charge and why a fixed finite restriction matrix cannot encode it.
