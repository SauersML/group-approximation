---
rg: 2
id: subexponential-complexity-zd-subshift-rank-model-proof
kind: route
target: subexponential-complexity-zd-subshift-rings-have-rank-models
requires:
  - subexponential-growth-simple-algebras-have-rank-models
artifacts:
  - research/artifacts/un-open-4-amenable-rank-models-2026-09-13.md
title: Proof — the generator ball is bounded by the number of lattice translations times the pattern count
---

Generate `R = LC(X,F_q) ⋊ Z^d` by the letter cylinders `χ_([a])` together with the `2d` unit translations
`u_(±e_i)`. Using `u_g f = (f ∘ g^{-1}) u_g`, a word of length at most `m` normalizes to `f · u_g` with
`g ∈ B_m(Z^d)` and `f` a product of at most `m` translated letter cylinders, each supported in the cube
`[−m, m]^d`. So `f` lies in the span of the indicators of patterns on that cube, of dimension `p(2m+1)`, and

  `dim R_m ≤ |B_m(Z^d)| · p(2m+1)`.

With `|B_m(Z^d)| = O(m^d)` and `p(n)` polynomial, `dim R_m` is polynomial in `m`, so `R` has polynomial
growth, in particular subexponential. Apply `subexponential-growth-simple-algebras-have-rank-models`, whose
simplicity hypothesis holds for the minimal topologically free case.

The estimate is exactly the `d = 1` computation of `zero-entropy-pestov-ring-rank-model-proof` with the
window replaced by a cube and `2m+1` translations replaced by `|B_m(Z^d)|`.
