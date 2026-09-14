---
rg: 2
id: haagerup-no-wall-proof
kind: route
title: An atomic Kazhdan image is all finite-dimensional isotypic, so every compressor fixes the commutant
target: haagerup-targets-carry-no-relative-wall
requires: [kazhdan-images-in-haagerup-algebras-are-atomic, fd-isotypic-part-of-a-kazhdan-image-carries-no-wall]
---

Put `N = M cap sigma(Lambda)'`.

1. By `kazhdan-images-in-haagerup-algebras-are-atomic`, `sigma(Lambda)''` is a
   direct sum of matrix algebras, so `sigma|Lambda` is a direct sum of
   finite-dimensional representations. Every finite-dimensional
   subrepresentation lies in the range of `sum_rho sigma(p_rho)`, so the
   isotypic projection `z` of `fd-isotypic-part-of-a-kazhdan-image-carries-no-wall`
   equals `1`.
2. For each `t in P_Lambda`, `(FIW1)` with `z = 1` gives
   `N = M cap sigma(t Lambda t^(-1))' = Ad sigma(t)(N)`, the last equality
   because `Ad sigma(t)` is an automorphism of `M` carrying `sigma(Lambda)` onto
   `sigma(t Lambda t^(-1))`.
3. The set `{g in G : Ad sigma(g)(N) = N}` is a subgroup containing
   `P_Lambda`, hence equal to `G`. This is `(HNW1)`.
4. Suppose `Lambda` is not normal. If every `t in P_Lambda` normalized
   `Lambda`, the group `P_Lambda` generates would normalize it, and that group
   is `G`. So some `t in P_Lambda` has `t Lambda t^(-1) < Lambda` strictly, i.e.
   `Lambda < t^(-1) Lambda t`. If `(x_i)` had common commutation stabilizer
   `Lambda`, each `x_i` would lie in `N`, so by `(HNW1)` each `sigma(t) x_i sigma(t)^*`
   lies in `N`. For `gamma in Lambda` this says `sigma(t^(-1) gamma t)` commutes
   with every `x_i`, so `t^(-1) Lambda t` is contained in the stabilizer
   `Lambda`, a contradiction.
