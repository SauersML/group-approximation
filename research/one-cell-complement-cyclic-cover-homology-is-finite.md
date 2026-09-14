---
rg: 2
id: one-cell-complement-cyclic-cover-homology-is-finite
kind: claim
title: The infinite cyclic cover of a one-cell complement has zero second homology, and over every field its first homology is finite-dimensional with t − 1 invertible
distinct_from:
  contractible-complex-minus-cell-has-cyclic-homology: that computes the homology of the one-cell complement itself; this computes the homology of its infinite cyclic cover as a module over the Laurent polynomial ring.
  wedges-of-spheres-have-free-cyclic-cover-homology: that shows the cyclic-cover homology of a wedge of spheres is free over the Laurent ring; this shows the cyclic-cover homology of a one-cell complement is torsion in degree one and zero in degree two.
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

**ESTABLISHED** through `one-cell-cyclic-cover-homology-proof`.

Let `L` be a finite connected contractible 2-complex, `e` an open 2-cell of `L`, `K = L − e`,
`G = π₁(K)`, `φ : G ↠ Z` the abelianization, and `N = ker φ`. Let `K_∞ → K` be the connected
infinite cyclic cover belonging to `φ`, so `π₁(K_∞) = N`, with deck generator `t`. Then:

1. `H₂(K_∞; Z) = 0`.
2. For every field `F`, `H₂(K_∞; F) = 0`, and `H₁(K_∞; F) = H₁(N; F)` is a finitely generated
   torsion `F[t, t⁻¹]`-module. In particular `dim_F H₁(N; F) < ∞`.
3. `t − 1` acts invertibly on `H₁(K_∞; F)` for every field `F`, and on `N^ab = H₁(K_∞; Z)`.

## What this settles for the L² question

The rational Alexander module of every one-cell complement is torsion and finite-dimensional
over `Q`. So a hypothesis such as "the infinite cyclic cover has finite-dimensional rational
first homology" holds for **every** one-cell complement. It cannot be the missing ingredient for
`one-cell-complement-groups-have-vanishing-first-l2-betti`.

The same rational profile also occurs without vanishing, so any proof has to use more than the
homology of `K_∞`. Take `K' = S¹ ∨ P`, where `P` is the presentation complex of
`⟨x, y | x² = y³ = (xy)⁵⟩`. That is a balanced presentation of a finite perfect group of order 120;
the order is recalled, not pinned. Then:

- `χ(K') = 0`, `H₁(K') ≅ Z` and `H₂(K') = 0`;
- `K'_∞` is a line with a copy of `P` wedged at each integer, so its rational `H₁` and `H₂` are zero;
- `π₂(K') ≠ 0`. The universal cover of `P` is simply connected with Euler characteristic 120, so its
  `H₂ = π₂` is nonzero, and `P` is a retract of `K'`.

`π₁(K') = Z * π₁(P)` is infinite, so the contrapositive of
`finite-2-complex-with-zero-second-l2-betti-is-aspherical` gives `b₁^(2)(π₁K') > 0`. By Kervaire
for finite groups (Gerstenhaber--Rothaus; recalled, not pinned here), `K'` is not a one-cell
complement. The gap is therefore the weight-one property itself.

## Calibration

`BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩` is a one-cell complement: adding the relator `t` gives a balanced
presentation of the trivial group whose complex has χ = 1 and `H₂ = 0`. Here `N = Z[1/2]` with `t`
acting as multiplication by 2:
- `N ⊗ Q = Q` and `t − 1 = 1`;
- `N ⊗ F₂ = 0`;
- `N ⊗ F_p = F_p` for odd `p`, and `t − 1 = 1`.

Items 1–3 hold, and `N` itself is not finitely generated.
