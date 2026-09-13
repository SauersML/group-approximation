---
rg: 2
id: isometry-compression-of-k1-trivial-unitary-is-null
kind: claim
title: Compressing a K1-trivial unitary by an isometry with properly infinite full defect gives a null unitary
distinct_from:
  trivial-unit-class-lxi-iff-universal-halving-homotopy: that uses a Cuntz pair, so it needs trivial unit class; this uses one isometry with properly infinite full defect, so it applies when [1] is nonzero, as in J + iota_1(T_2)
---

Let `A` be a unital C\*-algebra and `S ∈ A` an isometry such that `1 − SS^*` is properly infinite and
full. For `u ∈ U(A)` put `C_S(u) = SuS^* + (1 − SS^*)`. Then:

1. `[C_S(u)] = [u]` in `K_1(A)`;
2. if `[u] = 0`, then `C_S(u) ∈ U_0(A)`;
3. so `A` is K1-injective iff `u ~_h C_S(u)` in `U(A)` for every `u` with `[u] = 0`.

More generally, let `p` be a projection with `1 − p` properly infinite and full, and `v ∈ U(pAp)`. If
`[v + (1 − p)] = 0` in `K_1(A)`, then `v + (1 − p) ∈ U_0(A)`.

The unit axiom for one isometry therefore needs no Cuntz pair and no hypothesis on the unit class.
Consequence for the Toeplitz defect ideal: `defect-ideal-connected-iff-one-isometry-unit-axiom`.
