---
rg: 2
id: jacobson-amenable-symbol-subgroups-amenable-proof
kind: route
title: The symbol kernel is locally finite, so amenability passes both ways, and the compressor's symbol is a scalar on the Kazhdan block
target: jacobson-amenable-symbol-subgroups-are-amenable
requires:
  - binary-jacobson-mark-dichotomy-holds-from-rank-two
artifacts:
  - research/artifacts/jacobson-rank-radical-support-bound-and-symbol-firewall-2026-09-12.md
---

## Why sufficient

Artifact Section 3.

- **Locally finite kernel.** The kernel of `J -> F_2[z, z^(-1)]` is the span of the `e_ab = S^a Q T^b`
  (`binary-jacobson-mark-dichotomy-holds-from-rank-two`). So `ker pi` consists of matrices `g` whose
  `g - 1` has finitely many nonzero entries over `N x {1,...,n}`. Finitely many such matrices
  preserve a finite coordinate span and fix every other basis vector. So they generate a finite
  group.
- **Theorem 3.** `B ∩ ker pi` is amenable. Amenable-by-amenable is amenable, and quotients of
  amenable groups are amenable.
- **The compressor.** The off-diagonal entries of `u` are `e`, `et`, `et^2`, which lie in the kernel,
  and its diagonal is `(s, s, s, t^3)`. So `pi(u)` is the scalar `z` on coordinates `1, 2, 3`, and it
  centralizes `pi(EL_3(J))`. Hence `pi(<ker pi, u, Lambda>)` is a quotient of `Z x pi(Lambda)`.
- **Tilted constants.** Conjugation by `diag(z, z^2, z^3)` multiplies `x_ij(r)` by `z^(i-j)`. So it
  sends the simple root elements `x_12(1)`, `x_23(1)` and their negatives to `x_12(z^(-1))`,
  `x_23(z^(-1))`, `x_21(z)`, `x_32(z)`, and `SL_3(F_2)` to a finite group.
- **Faithful models.** A permutation matrix `P` with at most `eps n` fixed points has
  `rk(P - 1) = n - #cycles >= (1 - eps) n/2`. Sofic approximations give approximately multiplicative
  permutation matrices, hence injective rank models over any field.
