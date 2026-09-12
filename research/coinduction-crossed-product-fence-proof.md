---
rg: 2
id: coinduction-crossed-product-fence-proof
kind: route
title: Identify the stabilizer coordinate algebra with its faithful crossed product
target: coinduction-retains-crossed-product-not-relation
requires:
  - free-actor-extensions-cannot-host-nonce-relation
---

Use the equivariant-function model of coinduction.  Evaluation at the identity
coset identifies one coordinate algebra `A_0` with `L^infinity(X)`.  The
subgroup `Gamma` fixes its coset and acts on that coordinate by the original
action.  Hence `A_0` and `{u_g:g in Gamma}` satisfy the source covariance
relations.

The canonical expectation of the ambient crossed product onto
`L^infinity(Y)` kills every nonidentity `Lambda` Fourier coefficient.  Its
restriction to finite sums `sum_(g in Gamma) a_g u_g`, with `a_g in A_0`, is
therefore exactly the canonical faithful trace and expectation of
`A_0 rtimes Gamma`.  The covariant homomorphism is consequently injective and
extends normally, proving `(CR1)`.

For the Manzoor realization `Gamma=F`, the established
`free-actor-extensions-cannot-host-nonce-relation` says this source crossed
product is CE while the relation algebra is non-CE and the algebraic
stabilizer-forgetting quotient is singular.  Since the coinduced coordinate
copy is trace faithful, it retains the former and cannot factor through the
latter.  No assumption on the larger actor `Lambda` changes this coordinate
calculation.

