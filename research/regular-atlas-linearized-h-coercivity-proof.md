---
rg: 2
id: regular-atlas-linearized-h-coercivity-proof
kind: route
title: Equal kernels of two finite quadratic forms give a generalized eigenvalue bound
target: regular-atlas-linearized-h-coercivity
requires:
  - regular-atlas-boundary-tangent-is-h-fixed
---

On one copy of the finite regular tangent representation define positive
semidefinite forms

```text
A = sum_j B_j^* B_j,
H = sum_ell C_ell^* C_ell.
```

`regular-atlas-boundary-tangent-is-h-fixed` says exactly

```text
ker(A)=ker(H).
```

Restrict to the orthogonal complement of this common kernel.  There `A` is
positive definite.  The unit sphere is compact, so the generalized Rayleigh
quotient

```text
<X,HX>/<X,AX>
```

has a finite maximum `C_lin`.  Equivalently `H <= C_lin A` as quadratic forms.
This is `(LIN-H)` on one regular tangent copy.

The derivative representation for an external multiplicity is a direct sum of
copies of the same finite `A_8` sectors, and both `A` and `H` amplify by the
identity on the multiplicity space.  A quadratic-form inequality is preserved
under direct sums and tensoring by an identity, with the **same** constant.
Therefore `C_lin` is independent of `k`.