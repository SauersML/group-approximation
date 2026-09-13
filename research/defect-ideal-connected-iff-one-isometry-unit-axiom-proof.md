---
rg: 2
id: defect-ideal-connected-iff-one-isometry-unit-axiom-proof
kind: route
title: K_1(B_J) = 0, the isometry-compression lemma, and the O_2-quotient lifting lemma
target: defect-ideal-connected-iff-one-isometry-unit-axiom
requires: [isometry-compression-of-k1-trivial-unitary-is-null, toeplitz-defect-ideal-connected-iff-extension-k1-injective, o2-quotient-extension-ideal-k1-injective-iff-algebra]
---

- **`S = iota_1(s_2)` qualifies.**
  - `B_J` is unital and properly infinite (`toeplitz-defect-ideal-connected-iff-extension-k1-injective`,
    item 1).
  - `1 − SS^* = iota_1(s_1s_1^*) + e ≥ iota_1(s_1s_1^*)`, and `iota_1(s_1)` implements
    `iota_1(s_1s_1^*) ~ 1`.
  - A projection `r` with `1 ≲ r ≤ 1` in a properly infinite unital algebra is properly infinite and
    full: `r ⊕ r ≲ 1 ⊕ 1 ≲ 1 ≲ r`, and `1 ≲ r` gives fullness.
- **Item 1.**
  - `K_1(B_J) = 0` (same node, item 2: `K_*(B_J) ≅ (Z, 0)`), so every `u ∈ U(1+J) ⊆ U(B_J)` has
    `[u] = 0`.
  - By `isometry-compression-of-k1-trivial-unitary-is-null`, item 2, `C_S(u) ∈ U_0(B_J)`.
  - `C_S(u) = S(1 + x)S^* + 1 − SS^* = 1 + SxS^*`, and `SxS^* ∈ J` because `J` is an ideal of
    `A_T ⊇ B_J`. So `C_S(u) ∈ U(J~) ∩ U_0(B_J)`.
  - `B_J/J ≅ O_2`, so `o2-quotient-extension-ideal-k1-injective-iff-algebra`, item (a), gives
    `U(J~) ∩ U_0(B_J) = U_0(J~)`.
- **Item 2.**
  - (⟹) Both `u` and `C_S(u)` lie in the connected group `U(J~)`.
  - (⟸) `u ~_h C_S(u) ∈ U_0(J~)`, so `u ∈ U_0(J~)`. Every unitary of `J~` is a scalar multiple of an
    element of `U(1+J)`. Square.

**Where the earlier "under halving" came from.** Artifact part 2 §4 made `ψ(u) = SuS^* + iota_1(p_3)`
null inside the corner `pB_Jp` with `p = 1 − iota_1(s_1s_1^*)`, which has trivial unit class, and that
needed halving. Nullness in `B_J` itself only needs room for a stable null-homotopy under
`1 − SS^*`, and `B_J` has that room.
