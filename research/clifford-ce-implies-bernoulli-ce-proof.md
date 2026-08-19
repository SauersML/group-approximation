---
rg: 2
id: clifford-ce-implies-bernoulli-ce-proof
kind: route
title: Diagonal doubling cancels the two Clifford signs
target: clifford-ce-implies-bernoulli-ce
requires: []
artifacts:
  - notes/TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md
---

Complete written argument in the artifact, `(DCK4)--(DCK14)`.  For `x!=y`,
`(c_y c_x) tensor (c_y c_x)=(-c_x c_y) tensor (-c_x c_y)`, so the diagonal
Majoranas commute; each is a self-adjoint unitary; the joint moments are the
squares of the Clifford moments, hence `0` on every nonempty monomial, which
are exactly the Fourier moments of independent Haar signs; the diagonal
implementers `u_g tensor u_g` permute them and have vanishing trace off the
identity.  A trace-preserving embedding of a von Neumann algebra into a
Connes-embeddable one is inherited by subalgebras, and tensor squares of
Connes-embeddable algebras are Connes embeddable.
