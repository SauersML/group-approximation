---
rg: 2
id: binary-cyclic-corner-fullness-ascends-from-thompson-v
kind: route
title: A full order-three averaging idempotent over V gives the binary cyclic corner over the Leavitt units
target: binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
requires:
  - thompson-v-order-three-averaging-idempotent-is-full
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md
---

Artifact Lemma 1.1 and Corollary 3.2(1).

1. `k = (00, 01, 1) -> (0, 10, 11)` satisfies `k h k^(-1) = g`, where `g = (0, 10, 11) -> (10, 11, 0)`. So a
   solution `c e_h b = 1` in `F_2[V]` gives `(c k^(-1)) e_g (k b) = 1` in `F_2[V]`.
2. By the second requirement, `V <= R^x` with `R = L_(F_2)(1,2)`, through `x -> Σ S[b_i] T[a_i]`. This
   induces an injective unital algebra map `F_2[V] -> F_2[R^x]`.
3. The element `(0, 10, 11) -> (10, 11, 0)` goes to `S[10] T[0] + S[11] T[10] + S[0] T[11]`. With
   `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, this is `s_2 t_1 + s_3 t_2 + s_1 t_3`, the permutation unit `g`
   of the target. So `e_g` goes to the target's `e = 1 + [g] + [g²]`, and the solution carries over.

The direction of composition matters only for which of `k` and `k^(-1)` conjugates. `e_h = e_(h^(-1))`, so
either orientation gives a solution.
