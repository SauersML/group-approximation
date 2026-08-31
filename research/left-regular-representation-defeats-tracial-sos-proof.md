---
rg: 2
id: left-regular-representation-defeats-tracial-sos-proof
kind: proof
title: Test every universal tracial head estimate on the left regular tuple
target: jacobson-head-collapse-is-not-a-universal-tracial-identity
requires:
  - binary-jacobson-head-retaining-homomorphisms-are-faithful
---

The head `w=x_13(1-ST)` is a nonidentity element of `G). It is an
involution, but only nonidentity is needed below. The canonical trace on
the group von Neumann algebra satisfies

```text
tau_G(lambda(g))=0              for every g!=1.          (JUT3)
```

Therefore

```text
||lambda(w)-1||_2^2
 =tau_G((lambda(w)-1)^*(lambda(w)-1))
 =2-2 Re tau_G(lambda(w))
 =2.                                                     (JUT4)
```

Choose the tuple `U_x=lambda(x)`, indexed by the generators of the
fixed presentation. Since `lambda` is a genuine group
homomorphism,

```text
r(U)=1                         for every r in R.          (JUT5)
```

If `(JUT2)` held in every finite tracial von Neumann algebra, then
`(JUT4)` and `(JUT5)` would give

```text
sqrt(2) <= omega(0)=0,
```

a contradiction.

The same substitution applies to any proposed derivation assembled
from identities and positivity rules valid in arbitrary finite
tracial von Neumann algebras. This includes tracial
sum-of-squares manipulations and determinant or trace-moment
inequalities at that level of generality.

There is no conflict with a matrix-only estimate. A uniform matrix
estimate passes to normalized-Hilbert--Schmidt matrix ultraproducts,
not automatically to `L(G)`. Whether the canonical group trace
factors through such an ultraproduct is exactly the hyperlinearity
question under attack. Thus replacing a genuinely matricial argument
by a universal tracial one would assume away the only possible
separation mechanism.
