---
rg: 2
id: berend-dual-circles-have-infinite-rokhlin-dimension
kind: claim
title: Every infinite closed subgroup of the dual torus acts on the Berend algebra and its ideals with infinite Rokhlin dimension
distinct_from:
  stw99-lxxxvi-berend-groups-decomposition-rank: that asserts infinite decomposition rank of the Berend algebra; this proves only that the dual-action Rokhlin-dimension transfer cannot supply it.
  berend-proper-quotients-have-decomposition-rank-at-most-two: that bounds the decomposition rank of proper quotients; this uses finite-orbit quotients only as unital equivariant images on which the dual action is inner.
  ghs-z2-commuting-rokhlin-dimension-one-dual-sai: that imports Gardella--Hirshberg--Santiago results for Z_2-actions; this is an infinite-Rokhlin-dimension computation for dual torus actions on a specific group algebra.
artifacts:
  - research/artifacts/berend-dual-circle-rokhlin-obstruction-2026-09-16.md
---

Let `L = Z[a]` with `a^3 + a^2 - 2a - 1 = 0`, and let `Γ = Σ ≅ Z^2` be
Eckhardt's unit group, as in
`berend-torus-actions-give-strongly-qd-polycyclic-groups`. Put
`A = C*(L ⋊ Γ) = C(T^3) ⋊ Γ`, and let `\hat α` be the dual action of
`\hat Γ ≅ T^2`, given by `\hat α_χ(f u_γ) = χ(γ) f u_γ`.

Let `S ≤ \hat Γ` be a closed subgroup which is either infinite, or finite
of order divisible by `2` or `3`. Then for every nonzero `S`-invariant
closed ideal `I ⊆ A`, including `I = A`,

`dim_Rok(\hat α|_S on I) = dim^c_Rok(\hat α|_S on I) = ∞`.

Here `dim_Rok` and `dim^c_Rok` are the Rokhlin dimensions of
Gardella--Hirshberg--Santiago, arXiv:1709.00222, Definition 1.3, without and
with commuting towers. The same conclusion holds for `\hat α|_S ⊗ id` on
the minimal tensor product `A ⊗ D` for every nonzero unital `D`.

In particular, every closed one-dimensional `S` has infinite
commuting-tower Rokhlin dimension. Hence
`berend-some-dual-circle-has-finite-rokhlin-dimension` is false, and the
Rokhlin transfer `berend-case-from-finite-dual-rokhlin-dimension` gives
nothing. No statement about `dr(A)` itself is made.
