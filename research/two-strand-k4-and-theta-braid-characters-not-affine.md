---
rg: 2
id: two-strand-k4-and-theta-braid-characters-not-affine
kind: claim
title: "Two-strand braid groups of K_4 and of the theta graph have real characters induced by no function on hyperplane classes"
artifacts:
  - research/artifacts/graph-braid-hyperplane-affine-counterexample-2026-09-16.md
---

Let `Γ` be either:

- any subdivision of `K_4`, including `K_4` itself; or
- any subdivision of the theta graph `Θ_3` in which each of the three arcs
  has at least two edges.

Then the linear map from antisymmetric functions on oriented hyperplane
classes of `UD_2Γ` to `H^1(UD_2Γ; ℝ)` is not surjective. Its image has
dimension at most `β_1(Γ)` (3 for `K_4`, 2 for `Θ_3`), while
`b_1(UD_2Γ) ≥ 4` (resp. `≥ 3`).

`UD_2Γ` is connected, so `H^1(UD_2Γ; ℝ) = Hom(π_1 UD_2Γ, ℝ)`. When `Γ` meets
the subdivision hypothesis for `n = 2` (as in the root claim; `K_4` itself and
every `Θ_3` above do), `π_1 UD_2Γ = B_2Γ`, so some real character of `B_2Γ`
is not hyperplane-affine. This is exactly the setting of
`graph-braid-characters-are-hyperplane-affine`, which identifies
`Hom(B_nΓ, ℝ)` with `H^1(UD_nΓ; ℝ)`.
