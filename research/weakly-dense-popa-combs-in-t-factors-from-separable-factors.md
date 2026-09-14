---
rg: 2
id: weakly-dense-popa-combs-in-t-factors-from-separable-factors
kind: route
title: Weakly dense combs exist in property (T) factors because they exist in every separable II_1 factor, for instance L(SL_3(Z))
target: weakly-dense-popa-combs-exist-in-property-t-factors
requires:
  - separable-ii1-factors-have-weakly-dense-popa-combs
artifacts:
  - research/artifacts/sk-popa-input2-2026-09-14-part1.md
---

- **(T) factors with separable predual exist.** `SL_3(Z)` is an infinite ICC Kazhdan group, so `L(SL_3(Z))` is a II_1 factor with property (T) in the sense of Connes–Jones (Connes 1980; Connes–Jones, Bull. London Math. Soc. 17 (1985)). It has separable predual. The same holds for `L(G_X)` (`G_X` infinite simple Kazhdan, hence ICC).
- **Apply the general claim.** By `separable-ii1-factors-have-weakly-dense-popa-combs`, such a factor contains a weakly dense unital C*-subalgebra with a comb. This is the target.
