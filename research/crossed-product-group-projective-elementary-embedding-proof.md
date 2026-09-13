---
rg: 2
id: crossed-product-group-projective-elementary-embedding-proof
kind: route
title: Whitehead's identity puts diag(v, v^-1) in E_2, and conjugating x_13(1) detects central units
target: crossed-product-group-embeds-in-projective-elementary-group
requires: []
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

Complete proof: artifact Section 2 (Lemma W).

1. **Whitehead.** `w(v) = x_12(v) x_21(-v^(-1)) x_12(v) = [[0, v], [-v^(-1), 0]]`, computed row by row in any unital
   ring. Then `w(v) w(-1) = diag(v, v^(-1))`.
2. **Injectivity.** `ι` is a homomorphism, injective because `θ` is.
3. **Centre.** `ι(g) x_13(1) ι(g)^(-1) = x_13(θ(g))`. So `ι(g)` central forces `θ(g) = 1`, hence `g = e`.
