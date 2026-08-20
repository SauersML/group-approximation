---
rg: 2
id: schur-toeplitz-root-mark-fd-invisibility-proof
kind: route
title: Intersect the torsion-root kernels and apply direct finiteness in the resulting finite quotient
target: schur-toeplitz-root-mark-is-fd-invisible
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
---

For each ordered pair `i!=j`, the commuting exponent-`p` unitaries in
`rho(x_ij(R_f))` are simultaneously diagonalizable and form a subgroup of
`mu_p^d`; their kernel has finite additive index. Intersect the twenty
kernels to obtain `A`, and let `I=R_f A R_f`. Since `A subset I`, the
additive group of `R_f/I` is finite.

For `a in A` and arbitrary coefficients `r,s`, successive Steinberg
commutators using indices outside the active root express
`x_ij(ras)` as a product of commutators containing a kernel root. Hence
`x_ij(I)` is killed for every root. The coefficient quotient is a finite
ring, so the relation `yx=1` forces `xy=1`; its image of
`P_f=1-xy` is zero. Therefore `P_f in I` and all roots `x_ij(P_f)`, including
the marked one, lie in the representation kernel.

Finally the natural map to `EL_5(R_f)` sends `x_12(P_f)` to
`1+E_12P_f`, which is nonidentity because the packet embedding keeps
`P_f!=0`.
