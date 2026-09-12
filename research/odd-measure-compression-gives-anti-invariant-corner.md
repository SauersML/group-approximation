---
rg: 2
id: odd-measure-compression-gives-anti-invariant-corner
kind: route
title: A subequivalence in the signed Thompson crossed product solves the anti-central corner equation
target: ternary-anti-invariant-swap-corner-is-full
requires:
  - odd-measure-crossed-product-unit-below-cylinder-idempotent
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - hadamard-unit-conjugates-swap-idempotent-to-cylinder
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

## Why sufficient

* `B = F_3[H] eps_-` is a subalgebra of `S_- = F_3[G] eps_-`, and it contains `q_[0]`
  (`signed-thompson-algebra-is-odd-measure-crossed-product`).
* So a solution of `c' q_[0] b' = eps_-` in `B` is one in `S_-`.
* By `hadamard-unit-conjugates-swap-idempotent-to-cylinder`, `[h] e_- [h]^-1 = q_[0]`. So
  `b = [h]^-1 b'` and `c = c' [h]` give `c e_- b = eps_-`.

Corollary 3 of the artifact.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 20 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
