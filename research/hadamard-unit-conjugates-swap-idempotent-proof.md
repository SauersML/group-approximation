---
rg: 2
id: hadamard-unit-conjugates-swap-idempotent-proof
kind: route
title: Compute the Hadamard conjugation in the two-by-two matrix picture of the Leavitt algebra
target: hadamard-unit-conjugates-swap-idempotent-to-cylinder
requires: []
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

* The isomorphism `R -> M_2(R)`, `x -> (t_i x s_j)`, sends `h` to `[[1,1],[1,-1]]` and `w` to
  `[[0,1],[1,0]]`.
* So `h^2 = 2 = -1 = z`, and `h w h^-1` goes to `[[1,0],[0,-1]]`, which is `s0 t0 - s1 t1 = tau_[1] = z tau_[0]`.
* In the group algebra, `[h] e_- [h]^-1 = eps_- 2(1 + [z][tau_[0]]) = q_[0]`, because `[z] eps_- = -eps_-`.
* `q_[1] = eps_- 2(1 + [tau_[0]])`. So `q_[0] + q_[1] = 4 eps_- = eps_-` and
  `q_[0] q_[1] = eps_- (1 - [tau_[0]]^2) = 0`.
* `w` swaps the two cylinders, so `w tau_[0] w = tau_[1]`.

Section 1 of the artifact.
