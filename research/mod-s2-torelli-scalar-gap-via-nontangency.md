---
rg: 2
id: mod-s2-torelli-scalar-gap-via-nontangency
kind: route
title: Split the genus-two HS Torelli scalar gap into a cone condition at 1 and a prime-to-three order on the finite branch
target: mod-s2-exact-representations-have-a-torelli-scalar-gap
requires:
  - mod-s2-separating-twist-character-semigroup-dichotomy
  - mod-s2-separating-twist-characters-are-nontangent-at-one
  - mod-s2-separating-twist-circle-group-has-order-prime-to-three
---

- By (D5) of `mod-s2-separating-twist-character-semigroup-dichotomy`, the cone condition
  `mod-s2-separating-twist-characters-are-nontangent-at-one` makes `G_2 = mu_m` finite.
- By `mod-s2-separating-twist-circle-group-has-order-prime-to-three`, `3` does not divide `m`. So `omega` is
  not in `G_2`.
- (D3) turns this into a positive infimum of `||rho(t_s) - omega^(+-1) I||_2` over all finite-dimensional
  unitary `rho`, which is the target.

The two prerequisites are independent. The first excludes a concentration phenomenon near the identity. The
second is arithmetic on a finite group of roots of unity. The target, restricted to the finite branch, is
equivalent to the second.
