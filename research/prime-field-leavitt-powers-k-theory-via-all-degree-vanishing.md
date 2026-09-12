---
rg: 2
id: prime-field-leavitt-powers-k-theory-via-all-degree-vanishing
kind: route
title: Specialize all-degree K-vanishing of Leavitt tensor powers to K_1 and K_2 over each F_p
target: prime-field-leavitt-tensor-powers-have-trivial-k-theory
requires:
  - leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

`leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees` holds over every
field.

Take `k = F_p`, `d >= 3` and `n = 1, 2`. Then
`K_1(L_p^(⊗d)) = K_2(L_p^(⊗d)) = 0`, since non-connective and Quillen
`K`-theory agree in degrees `n >= 1`. ∎
