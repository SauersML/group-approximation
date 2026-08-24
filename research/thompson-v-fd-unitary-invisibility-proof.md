---
rg: 2
id: thompson-v-fd-unitary-invisibility-proof
kind: route
title: Combine simplicity with Malcev residual finiteness
target: thompson-v-has-no-nontrivial-fd-unitary-representation
requires:
  - thompson-v-not-lef
---

Cannon--Floyd--Parry prove that Thompson's `V` is infinite, finitely generated
and simple.  Suppose `rho:V -> U(d)` were nontrivial.  Its kernel is normal,
so simplicity makes `rho` injective.  Hence `V` is a finitely generated
subgroup of `GL_d(C)`.

By Mal'cev's residual-finiteness theorem, every finitely generated linear
group over a characteristic-zero field is residually finite.  Thus `V` would
be residually finite and hence LEF, contradicting the established claim
`thompson-v-not-lef`.  Therefore `rho` is trivial.
