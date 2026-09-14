---
rg: 2
id: char-two-jordan-square-root-needs-amplification
kind: claim
title: In characteristic 2 the unipotent Jordan block has no square root, but its doubled amplification does
distinct_from:
  amplified-algebraic-roots-for-nonsingular-equations: that is the universal approximate root premise; this is one exact degree-two instance showing the premise cannot be sharpened to exact roots without amplification.
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**ESTABLISHED** through `char-two-jordan-square-root-amplification-proof`.

Let `K` be any field of characteristic 2 and `J = [[1,1],[0,1]]`. Then:
1. no `T` in `GL_2(K')` satisfies `T^2 = J`, for any field `K' >= K`;
2. some `T` in `GL_4(K)` satisfies `T^2 = J (x) 1_2`.

So the nonsingular equation `t^2 c^{-1} = 1`, with constant `c = J`, has no
exact root at amplification `r = 1` over the algebraic closure, but has one at
`r = 2` over the prime field.
