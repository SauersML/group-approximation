---
rg: 2
id: hs-gap-failure-cheap-refinement
kind: claim
title: Every scalar HS gap failure admits a small-side refinement charged by that side's trace
---

Let `U_1,...,U_m` be unitaries in `M_d`, let `p!=0` be a projection, and put
`a_s=pU_sp`.  Normalize trace and Hilbert--Schmidt norm inside `pM_dp`.
If the scalar adjoint Poincare inequality with constant `kappa>0` fails on
this block, then there is a nonzero `q<p` with

```text
tau(q) <= tau(p)/2
```

such that, writing `r=p-q`, refining `p` to the two blocks `q,r` increases the
total ambient generator-boundary energy by less than

```text
4 sqrt(2m) kappa tau(q).                              (CHEAP)
```

The estimate is dimension-free and remains valid for spiky gap witnesses.
It does not by itself sum over a whole recursive decomposition; it supplies
the exact local charge that such a global potential must control.
