---
rg: 2
id: prime-field-leavitt-powers-k-theory-via-coherence
kind: route
title: Over every prime field, coherent Leavitt tensor powers kill K_1 and K_2 after one more factor
target: prime-field-leavitt-tensor-powers-have-trivial-k-theory
requires:
  - leavitt-tensor-powers-are-left-coherent
  - leavitt-tensor-global-dimension-bound
  - regular-coherent-coefficients-kill-leavitt-tensor-k-theory
---

The derivation of `leavitt-tensor-powers-k-theory-via-coherence` with `k = F_p`.
All three inputs are stated over an arbitrary field.

Let `R = L_p^(⊗(d-1))` with `d >= 3`.
1. `R` is left coherent, and right coherent through its involution.
2. `R` has finite global dimension `d − 1` on both sides, so it is regular
   coherent.
3. `K_n(R ⊗ L_p) = K_n(L_p^(⊗d)) = 0` for every `n >= 1`.
