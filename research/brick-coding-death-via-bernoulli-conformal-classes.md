---
rg: 2
id: brick-coding-death-via-bernoulli-conformal-classes
kind: route
title: A brick coding gives a spatial realization whose letter classes are square-complex cocycles, which rank-two H^1 puts in the degree plane
target: two-graph-brick-codings-die-when-square-complex-h1-has-rank-two
requires:
  - spatial-two-graph-realizations-in-g2n-leave-the-degree-plane
  - brick-coded-two-graph-full-groups-embed-in-brin-thompson
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
---

Full proof: Corollaries 3.3 and 3.4 of the artifact.

1. **Spatial realization.**
   - By `brick-coded-two-graph-full-groups-embed-in-brin-thompson`, a brick coding `φ`
     gives a homeomorphism `h : X_Λ -> ⊔_a C^m` with `h(λz) = φ(λ)h(z)`.
   - Chart `⊔_a C^m` into `C^m` by word tuples `π_a` whose bricks partition `C^m`.
   - Set `ι(λz, d(λ) - d(μ), μz) = (π_{r(λ)}φ(λ)h(z), k, π_{r(μ)}φ(μ)h(z))`, where `k` is the
     difference of word lengths.
   - Common extensions `(λν, μν)` give the same triple, so `ι` is a spatial realization.
2. **Letter classes in the plane.**
   - `n^ε_i(e) = #_ε(φ_i(e))` is a 1-cocycle on `K(Λ)` by (B2).
   - `dim H^1(K(Λ)) = 2` makes it `α d_1 + β d_2 + δg`.
   - Telescoping gives `N^ε_i∘ι = α d_1 + β d_2 + H∘r - H∘s` with
     `H(x) = ±g(r(x)) + #_ε(π_{r(x),i})` continuous.
   - This contradicts `spatial-two-graph-realizations-in-g2n-leave-the-degree-plane` (i).
3. **Block recodings.** `Λ^{[k]}` is a finite 2-graph without sources.
   - Its colour-1 paths of length `j` are the degree-`(j+k, k)` rectangles of `Λ`.
   - Every colour-1 path of `Λ` of length `j+k` lies under at least one of them, and
     distinct paths give distinct rectangles.
   - So `‖(M_1^{[k]})^j‖_Σ ≥ ‖M_1^{j+k}‖_Σ`, which gives `ρ(M_1^{[k]}) ≥ ρ(M_1) > 1`.
   - Apply (a) to `Λ^{[k]}`.
