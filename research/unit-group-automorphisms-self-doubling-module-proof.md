---
rg: 2
id: unit-group-automorphisms-self-doubling-module-proof
kind: route
title: Read the Leavitt relations as a direct sum decomposition of the free module
target: unit-group-is-automorphisms-of-a-self-doubling-module
requires: []
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
---

## Proof

Endomorphisms of `R_R` are left multiplications, so `End_R(R_R) = R` as
rings and `Aut_R(R_R) = R^x`.

The defining relations `t_is_j = delta_(ij)` and `s_1t_1 + s_2t_2 = 1` say
that the maps

```text
M --> M (+) M,   x |-> (t_1x, t_2x),
M (+) M --> M,   (y_1,y_2) |-> s_1y_1 + s_2y_2
```

are mutually inverse module maps: one composite is
`(t_i(s_1y_1 + s_2y_2))_i = (y_i)_i`, the other is
`s_1t_1x + s_2t_2x = x`.  So `M = M (+) M`, and iterating gives `M = M^(n)`
for every `n >= 1`.

Choosing the decomposition `M = M^(n)` identifies
`End_R(M^(n)) = M_n(End_R(M)) = M_n(R)`, and passing to automorphism groups
gives `GL_n(R) = Aut_R(M^(n)) = Aut_R(M) = R^x`.
