---
rg: 2
id: hadamard-unit-conjugates-swap-idempotent-to-cylinder
kind: claim
title: The Hadamard unit conjugates the ternary swap corner idempotent to a cylinder reflection idempotent
distinct_from:
  ternary-leavitt-swap-problem-splits-at-central-involution: that conjugates e_- to its complement eps_- - e_- by the sign unit d; this conjugates e_- to the idempotent of the cylinder reflection tau_[0] by the Hadamard unit h, turning the corner target into a subequivalence against a character idempotent of the reflection group.
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `eps_- = 2(1 - [z])`, `S_- = eps_- F_3[G]`,
`w = s0 t1 + s1 t0` and `e_- = eps_- 2(1 + [w])`. For a clopen `C` of Cantor space, let `P_C`
be its diagonal projection, `tau_C = 1 - 2 P_C` and `q_C = eps_- 2(1 - [tau_C])`.

* `h = s0 t0 + s0 t1 + s1 t0 - s1 t1` is a unit with `h^2 = z`, and `h w h^-1 = tau_[1] = z tau_[0]`.
* So `[h] e_- [h]^-1 = q_[0]` in `S_-`.
* `q_[0] + q_[1] = eps_-`, `q_[0] q_[1] = 0` and `[w] q_[0] [w] = q_[1]`.

Hence `ternary-anti-invariant-swap-corner-is-full` holds iff `eps_-` is Murray--von Neumann below
`q_[0]` in `S_-`, iff `[q_[0]] + [q_[0]] <= [q_[0]]` there. Proposition 1 of the artifact.
