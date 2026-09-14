---
rg: 2
id: one-cell-cyclic-cover-homology-proof
kind: route
title: Wang sequence of the infinite cyclic cover, structure of modules over a PID, and an Euler characteristic count
target: one-cell-complement-cyclic-cover-homology-is-finite
requires:
  - contractible-complex-minus-cell-has-cyclic-homology
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

Notation as in the target. `contractible-complex-minus-cell-has-cyclic-homology` gives
`χ(K) = 0`, `H₁(K; Z) ≅ Z` and `H₂(K; Z) = 0`, and says `φ` is onto `Z`, so `K_∞` is connected.

## 1. Field coefficients on `K`

By universal coefficients:
- `H₂(K; F) = H₂(K; Z) ⊗ F ⊕ Tor(H₁(K; Z), F) = 0`;
- `H₁(K; F) = H₁(K; Z) ⊗ F ⊕ Tor(H₀(K; Z), F) ≅ F`.

## 2. Wang sequence

Let `R = F[t, t⁻¹]` or `Z[t, t⁻¹]`, and let `C_*` be the cellular chain complex of `K_∞` with
coefficients in `F` (respectively `Z`). It is a complex of free `R`-modules of ranks `c₀, c₁, c₂`,
the cell counts of `K`, and `c₀ − c₁ + c₂ = χ(K) = 0`. There are no 3-cells.

Multiplication by `t − 1` is injective on free `R`-modules. Its cokernel `C_* ⊗_R R/(t − 1)` is the
cellular chain complex of `K`. The long exact sequence contains

  `H₂(K) → H₁(K_∞) --(t−1)--> H₁(K_∞) → H₁(K) → H₀(K_∞) --(t−1)--> H₀(K_∞)`.

## 3. `t − 1` is invertible on `H₁(K_∞)`

- **Injective.** `H₂(K) = 0` over `F` and over `Z`.
- **Surjective.** `H₀(K_∞) ≅ H₀(K)` is `F` (respectively `Z`) with `t` acting trivially, so `t − 1`
  is zero there, and `H₁(K) → H₀(K_∞)` is onto. That map is `F → F` (respectively `Z → Z`), and an
  onto map of this kind is injective. So `H₁(K_∞) → H₁(K)` is zero, which makes `t − 1` onto on
  `H₁(K_∞)`.

This proves item 3.

## 4. `H₁(K_∞; F)` is torsion and finite-dimensional

`R = F[t, t⁻¹]` is a principal ideal domain, and `H₁(K_∞; F)` is a subquotient of `C₁ ≅ R^{c₁}`, so
it is finitely generated: `H₁ ≅ R^r ⊕ T` with `T` torsion. If `r > 0`, then `coker(t − 1)` contains
`(R/(t − 1))^r ≠ 0`, against step 3. So `r = 0`. A finitely generated torsion `R`-module is a finite
direct sum of modules `R/(p)` with `p ≠ 0`, each finite-dimensional over `F`.

`H₁(K_∞; F) = H₁(N; F)` because `K_∞` is connected with `π₁(K_∞) = N`, and
`H₁(X; F) = π₁(X)^ab ⊗ F` for connected `X`.

## 5. `H₂(K_∞; F) = 0`

Tensor with the fraction field `F(t)`, which is flat over `R`. The alternating sum of the ranks of
`H_i(C_*)` equals `c₀ − c₁ + c₂ = 0`.
- `H₀(K_∞; F) ≅ R/(t − 1)` is torsion, of rank 0.
- `H₁` has rank 0 by step 4.

So `H₂` has rank 0. With no 3-cells, `H₂(K_∞; F) = ker(∂₂ : C₂ → C₁)` is a submodule of a free
module over a PID, hence free, of rank 0, hence zero.

## 6. `H₂(K_∞; Z) = 0`

`H₂(K_∞; Z) = ker(∂₂)` is a subgroup of the free abelian group `C₂(K_∞; Z)`, so it is torsion-free.
`Q` is flat over `Z`, so `ker(∂₂) ⊗ Q = ker(∂₂ ⊗ Q) = H₂(K_∞; Q)`, which is `0` by step 5. A
torsion-free abelian group with zero rationalization is zero. This proves item 1.

Items 2 and 3 are steps 3–5.
