---
rg: 2
id: kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding
kind: route
title: Kill the Kun--Thom wreath from unit-type rounding of the vertex
target: non-hyperlinear-group
requires:
  - theorem-e-vertex-rounds-to-unit-type-representations
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - kun-thom-wreath-carries-rigid-defect
artifacts:
  - research/artifacts/nh-h1-rounding-2026-09-12.md
---

Suppose the explicit Kun–Thom wreath `W = C_2 wr_(G/Γ) G` is hyperlinear, witnessed by a
trace-preserving `σ : W -> U(M)`, `M = prod_U M_n`.

1. Apply `theorem-e-vertex-rounds-to-unit-type-representations` to `σ|G`.
   `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` then shows that `σ(G)`
   normalizes `N = σ(Γ)' ∩ M`.
2. The base lamp `a_Γ` commutes with `Γ`, so `a_Γ ∈ N`. For a strict compressor `t`, normalization
   puts `a_(tΓ) = σ(t) a_Γ σ(t)^*` in `N`.
3. Every `γ ∈ Γ \ tΓt^(-1)` therefore commutes with `a_(tΓ)`. But `σ(γ) a_(tΓ) σ(γ)^* = a_(γtΓ)`
   is the lamp at a different coset, at normalized 2-distance `√2` in the canonical trace. This is
   the rigid defect of `kun-thom-wreath-carries-rigid-defect`.

This is a contradiction, so `W` is not hyperlinear. The route stays open while its first premise is
open.
