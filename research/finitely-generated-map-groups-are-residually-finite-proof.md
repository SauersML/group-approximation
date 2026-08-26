---
rg: 2
id: finitely-generated-map-groups-are-residually-finite-proof
kind: route
title: Mal'cev on the image of each separating representation
target: finitely-generated-map-groups-are-residually-finite
requires: []
---

Fix `1 != h in H` and a finite-dimensional unitary representation `rho` with
`rho(h) != 1`.  The image `rho(H) <= U(d) <= GL_d(C)` is a finitely generated
linear group, hence residually finite (Mal'cev, 1940), so there is a finite
quotient `psi : rho(H) -> F_h` with `psi(rho(h)) != 1`, and `psi o rho` is a
finite quotient of `H` separating `h`.  The converse is immediate from
permutation representations of finite quotients.  The simple case: a
nontrivial finite-dimensional unitary representation of a simple group has
trivial kernel, so the group is finitely generated linear, hence residually
finite, hence sofic.
