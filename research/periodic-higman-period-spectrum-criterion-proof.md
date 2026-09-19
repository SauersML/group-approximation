---
rg: 2
id: periodic-higman-period-spectrum-criterion-proof
kind: route
title: The period screen makes every finite quotient kill the protected base mark
target: periodic-higman-period-spectrum-criterion
requires:
  - periodic-higman-deep-torsion-fillings
  - periodic-higman-finite-images-are-perfect-or-trivial
---

Fix `m>=m_0` avoiding all divisors from `Sigma`, and take any homomorphism
`rho:G_m->Q` to a finite group.  The induced pair `(H,alpha)` has
`alpha^m=1`, so `ord(alpha)` divides `m`.  If `alpha` were nontrivial, its
order would belong to `Sigma`, contradicting the choice of `m`.  Therefore
`alpha=1`, and `periodic-higman-finite-images-are-perfect-or-trivial` gives
`H=1`.

Thus every finite quotient of `G_m` kills `a`.  On the other hand,
`periodic-higman-deep-torsion-fillings` says that `G_m` is word-hyperbolic
and that `a!=1` in it.  Hence `a` is a nonidentity element of the finite
residual of `G_m`, proving `(PH3)`.
