---
rg: 2
id: raag-kernel-dehn-function-below-bestvina-brady
kind: claim
title: Some RAAG has a finitely presented kernel onto Z with quadratic Dehn function while its Bestvina–Brady group has cubic Dehn function
distinct_from:
  stallings-bieri-groups-have-quadratic-dehn-function: that claim is the Carter–Forester theorem that the Stallings–Bieri kernels of products of free groups are quadratic; this one compares two different kernels of one RAAG
  bestvina-brady-dehn-function-classification: that claim is the classification of Dehn functions of Bestvina–Brady groups; this one uses it to compare the Bestvina–Brady group with another kernel
---

Let `P` be the path `C – D – E – F` and let `Γ = {A, B} * P` be its
suspension (`A`, `B` not adjacent, each adjacent to all of `C, D, E, F`), so
`A_Γ = F(A, B) × A_P`. Let `χ : A_Γ → Z` send `A, B` to `0` and `C, D, E, F`
to `1`. Then:

- `χ` is surjective and `K_χ = F(A, B) × BB_P ≅ F_2 × F_3` is finitely
  presented with Dehn function `≃ n^2`;
- `BB_Γ` is finitely presented with Dehn function `≃ n^3`.

So `δ_{BB_Γ} ⋠ δ_{K_χ}`.

More generally, the same holds for `Γ = T * Λ` with `T` a tree that is not a
star and `Λ` an irreducible graph with at least two vertices, `χ` equal to `1`
on `T` and `0` on `Λ`: then `K_χ = BB_T × A_Λ` has quadratic Dehn function and
`BB_Γ` has cubic Dehn function.

Status: established by `raag-kernel-dehn-function-below-bestvina-brady-proof`,
unreviewed as of 2026-09-13.
