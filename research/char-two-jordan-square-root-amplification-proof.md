---
rg: 2
id: char-two-jordan-square-root-amplification-proof
kind: route
title: A square root commutes with the regular unipotent and so is a polynomial in it; after doubling, a single nilpotent Jordan block squares to the right type
target: char-two-jordan-square-root-needs-amplification
requires: []
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

Write `N = J - 1`, so `N != 0` and `N^2 = 0`.

**Part 1.** Suppose `T^2 = J` with `T` in `GL_2(K')`. `T` commutes with
`T^2 = J`, hence with `N`. The centralizer of the nonzero nilpotent `N` in
`M_2(K')` is `{alpha 1 + beta N}`: writing `T = [[p,q],[s,u]]`, the equation
`TN = NT` forces `s = 0` and `p = u`. So `T = alpha 1 + beta N`, and
`T^2 = alpha^2 1 + 2 alpha beta N + beta^2 N^2 = alpha^2 1` in characteristic
2. That is a scalar, not `J`, contradiction.

**Part 2.** Let `M` be the `4 x 4` nilpotent Jordan block over `K`
(`M e_1 = 0`, `M e_{j+1} = e_j`), and `T_0 = 1 + M`, invertible. In
characteristic 2, `T_0^2 = 1 + 2M + M^2 = 1 + M^2`. Now `M^2` is nilpotent,
`(M^2)^2 = M^4 = 0`, and `rank(M^2) = 2`. So `M^2` has Jordan type `(2,2)`: a
nilpotent matrix with square zero is determined up to conjugacy over any
field by its rank.

`J (x) 1_2 - 1 = N (x) 1_2` is also nilpotent with square zero and rank 2.
Hence there is `S` in `GL_4(K)` with `S M^2 S^{-1} = N (x) 1_2`. Then
`T = S T_0 S^{-1}` satisfies `T^2 = S(1 + M^2)S^{-1} = 1 + N (x) 1_2 = J (x) 1_2`.
