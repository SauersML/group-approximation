---
rg: 2
id: faithful-unit-specialization-gives-z-linearity
kind: claim
title: A faithful specialization of a Laurent-polynomial representation at algebraic units makes the group Z-linear
---

Let `G` be a group and `rho: G -> GL_m(Z[x_1^{±1}, ..., x_k^{±1}])` a
homomorphism. Let `F` be a number field with ring of integers `O_F`, and let
`u_1, ..., u_k` be units of `O_F`. If the specialized homomorphism
`rho_u: G -> GL_m(O_F)`, obtained by substituting `x_i -> u_i`, is injective,
then `G` has an injective homomorphism into `GL_(m[F:Q])(Z)`.

The units matter: substituting a non-unit `u` makes `u^{-1}` appear, and the
image lies only in `GL_m(O_F[1/u])`.

Proof: `faithful-unit-specialization-gives-z-linearity-proof`.
