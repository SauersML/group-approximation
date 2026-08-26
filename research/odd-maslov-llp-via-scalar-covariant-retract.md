---
rg: 2
id: odd-maslov-llp-via-scalar-covariant-retract
kind: route
title: Transfer even-fibre LLP through a scalar-cochain covariant ucp retract
target: sp4-mod3-twisted-fibres-have-llp
requires:
  - sp2g-z-full-c-star-algebra-has-llp
  - metaplectic-half-class-has-an-exact-finite-model
---

**INVALIDATED ROUTE.**  The proposal was to weaken equivariant Morita
transport while keeping each odd canonical generator in the scalar
homogeneous line of the corresponding even generator:

```text
i(u_s^odd)=c_s(I_n tensor u_s^even),
```

with a split ucp retraction.  Such a retract would transfer LLP from the even
fibre.

`scalar-covariant-odd-even-ucp-retract-is-impossible` proves that the split
norm equality forces every `|c_s|=1`.  All generator images are then unitary,
the embedding is a star-homomorphism by multiplicative domain, and an even
finite-dimensional representation yields a forbidden odd one.  Allowing
matrix-valued homogeneous coefficients avoids this exact argument, but
`matrix-homogeneous-ucp-retracts-can-hide-defect` shows why it no longer
forces multiplicativity.


