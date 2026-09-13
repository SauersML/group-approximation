---
rg: 2
id: toeplitz-defect-ideal-connected-via-almost-commuting-projection
kind: route
title: An almost commuting properly infinite full projection makes each unitary of 1 + J null (BRR Lemma 2.4(ii) plus quotient lifting)
target: toeplitz-defect-ideal-unitization-k1-injective
requires: [toeplitz-defect-ideal-almost-commuting-projection-axiom, brr-commutator-criterion-null-unitary, toeplitz-defect-ideal-connected-iff-extension-k1-injective, o2-quotient-extension-ideal-k1-injective-iff-algebra]
---

Let `u ∈ U(1 + J)`.
- `K_1(B_J) = 0` (`toeplitz-defect-ideal-connected-iff-extension-k1-injective`, item 2), so `[u] = 0` in
  `K_1(B_J)`.
- `toeplitz-defect-ideal-almost-commuting-projection-axiom` gives a projection `p ∈ B_J` with `p` and
  `1 − p` properly infinite and full, and `||up − pu|| < 1`.
- `brr-commutator-criterion-null-unitary` in `A = B_J` gives `u ∈ U_0(B_J)`.
- `B_J/J ≅ O_2`, so `o2-quotient-extension-ideal-k1-injective-iff-algebra`, item (a), gives
  `u ∈ U_0(J~)`.

Every unitary of `J~` is a scalar multiple of one in `U(1+J)`, so `U(J~)` is connected.
