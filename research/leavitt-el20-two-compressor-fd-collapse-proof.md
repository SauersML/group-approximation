---
rg: 2
id: leavitt-el20-two-compressor-fd-collapse-proof
kind: route
title: Compare the dimensions of the two commuting conjugate child algebras
target: leavitt-el20-two-compressor-fd-representations-kill-mark
requires:
  - leavitt-diagonal-compression-is-elementary-amenable
---

Let `pi:B_EL->U(d)` and put

```text
A=C^*(pi(Lambda)),             A_i=C^*(pi(Psi_i(Lambda))).
```

Each `A_i` is a subalgebra of `A`.  Compressor covariance gives
`A_i=Ad(pi(tau_i))(A)`, so `dim A_i=dim A`.  Finite-dimensionality therefore
forces `A_0=A=A_1`.  The complementary child groups commute, whence
`[A_0,A_1]=0`; consequently `A` is commutative.

The group `Lambda` is an increasing union of the perfect groups
`GL_5(F_2)^(2^k)`, and is therefore perfect.  Its image in the abelian unitary
group of `A` is trivial.  In particular `pi(z)=1`.
