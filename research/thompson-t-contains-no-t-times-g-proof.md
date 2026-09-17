---
rg: 2
id: thompson-t-contains-no-t-times-g-proof
kind: route
title: The G-factor of a copy of T x G centralizes a copy of T
target: thompson-t-contains-no-t-times-g
requires:
  - thompson-t-copies-of-t-have-trivial-centralizer
---

Let `φ : T × G → T` be injective. Put `A = φ(T × 1)` and `B = φ(1 × G)`.
Since `φ` is injective, `A ≅ T` and `B ≅ G`. Every element of `T × 1`
commutes with every element of `1 × G`, so `B ≤ C_T(A)`. By
`thompson-t-copies-of-t-have-trivial-centralizer`, `C_T(A) = 1`. So `B = 1`,
and `G = 1` because `φ` is injective. ∎
