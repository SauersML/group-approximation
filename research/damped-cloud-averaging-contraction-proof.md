---
rg: 2
id: damped-cloud-averaging-contraction-proof
kind: route
title: Interpolate affinely to cloud means and use exact vanishing of every face residual
target: damped-cloud-averaging-contracts-from-exact-faces
requires:
  - expander-cloud-reduction-preserves-pauli-dimension-gap
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
---

Inside one cloud write `D_v=A_v-S`.  Since `A_v^2=I` and
`sum_v lambda_vD_v=0`,

```text
 V=sum_v lambda_vD_v^2=I-S^2.                          (DCAP1)
```

The Hilbert-valued expander Poincare inequality gives

```text
 sum_(i,v)nu_i lambda_(i,v)||D_(i,v)||_2^2
 <=lambda_eq^(-1)E_eq(0).                              (DCAP2)
```

Because the same `S_i` is used throughout a cloud,
`X_(i,u)(t)-X_(i,v)(t)=(1-t)(A_(i,u)-A_(i,v))`, proving
the first identity in `(DCA2)` and `(DCA4)`.

Every face word vanishes at `t=0`.  Fixed-width telescoping for contractions
therefore gives

```text
 ||prod_a X_(i_a,v_a)(t)-prod_a A_(i_a,v_a)||_2^2
 <=m t^2 sum_a||D_(i_a,v_a)||_2^2.                    (DCAP3)
```

The identical two-term expansion bounds a created commutator square by a
fixed multiple of `t^2` times the endpoint movements.  Bounded occurrence
and `(DCAP2)` control the normalized sums.

For the involution layer, direct expansion gives

```text
 I-X_v(t)^2=t(1-t)D_v^2+t(I-S^2).                     (DCAP4)
```

All terms are positive.  Since `||D_v||_infinity<=2` and `0<=V<=I`,
the squared normalized-HS average of `(DCAP4)` is at most a fixed multiple
of

```text
 t^2 sum_v lambda_v tau(D_v^2),
```

and hence is paid by `(DCAP2)`.  This proves the second inequality in
`(DCA2)`.  Finally minimize `(1-t)^2+C_0t^2`; its minimizer and minimum are
exactly `t_0` and `rho_0` in `(DCA3)`.
