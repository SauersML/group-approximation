---
rg: 2
id: leavitt-tensor-powers-k-theory-via-all-degree-vanishing
kind: route
title: Specialize all-degree K-vanishing of Leavitt tensor powers to K_1 and K_2 over F_2
target: leavitt-tensor-powers-have-trivial-k-theory
requires:
  - leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees` gives
`K_n(L_k(1,2)^(⊗d)) = 0` for every field `k`, every `d >= 1` and every `n ∈ Z`.

Take `k = F_2`, `d >= 3` and `n = 1, 2`. For `n >= 1`, non-connective `K`-theory
agrees with Quillen `K`-theory, so `K_1(L^(⊗d)) = K_2(L^(⊗d)) = 0`. ∎
