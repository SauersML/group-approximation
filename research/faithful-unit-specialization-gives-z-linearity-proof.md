---
rg: 2
id: faithful-unit-specialization-gives-z-linearity-proof
kind: route
title: Restrict scalars from O_F to Z
target: faithful-unit-specialization-gives-z-linearity
requires: []
---

Since each `u_i` is a unit, the substitution `x_i -> u_i` is a ring
homomorphism `Z[x_1^{±1}, ..., x_k^{±1}] -> O_F`. Applied entrywise it gives a
ring homomorphism `M_m(Z[x^{±1}]) -> M_m(O_F)`, which sends invertible
matrices to invertible matrices. So `rho_u` is a homomorphism into
`GL_m(O_F)`.

`O_F` is a free `Z`-module of rank `d = [F:Q]`. Fix a basis. Left
multiplication by `a in O_F` is a `Z`-linear endomorphism, with matrix
`L(a) in M_d(Z)`, and `a -> L(a)` is a ring homomorphism. It is injective,
because `L(a)(1) = a`. Replacing every entry `a` of an `m × m` matrix over
`O_F` by the block `L(a)` gives an injective ring homomorphism
`M_m(O_F) -> M_(md)(Z)`. It maps `GL_m(O_F)` into `GL_(md)(Z)`, since ring
homomorphisms preserve inverses. The composite
`G -> GL_m(O_F) -> GL_(md)(Z)` is injective. ∎
