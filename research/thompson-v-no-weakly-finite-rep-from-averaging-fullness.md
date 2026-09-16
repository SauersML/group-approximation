---
rg: 2
id: thompson-v-no-weakly-finite-rep-from-averaging-fullness
kind: route
title: A full order-three averaging idempotent kills every directly finite characteristic-two representation of V
target: thompson-v-has-no-weakly-finite-char-two-representation
requires:
  - thompson-v-order-three-averaging-idempotent-is-full
  - thompson-v-finitely-presented-infinite-simple
artifacts:
  - research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md
---

Artifact Theorem W_V, the chain (a) => (c_DF) => (d_DF) => (d).

1. Let `ρ : V -> W^x` be a homomorphism, with `W` directly finite and `2 · 1_W = 0`. It extends to a unital
   ring homomorphism `φ : F_2[V] -> W`.
2. Take `c e_h b = 1` from the first requirement. Put `X = φ(c e_h)` and `Y = φ(e_h b)`. Then `XY = 1`, so
   `YX = 1` by direct finiteness.
3. So `φ(e_h)` has a right inverse `φ(b c e_h)` and a left inverse `φ(e_h b c)`. An invertible idempotent
   is `1`, so `φ(e_h) = 1`.
4. With `u = φ(h)`, `u + u² = 0`, hence `u² = u` in characteristic two. `u` is a unit, so `u = 1`.
5. `ker ρ` is a normal subgroup containing `h != 1`, so it is `V` by the second requirement.

Only size-one direct finiteness is used, so this proves the stronger directly finite form (artifact
Remark 2.1). Together with `thompson-v-averaging-fullness-from-no-weakly-finite-rep` it forms an intended
cycle: the claim and the target are equivalent, and neither route establishes either one.
