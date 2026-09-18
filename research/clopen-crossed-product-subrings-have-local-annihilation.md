---
rg: 2
id: clopen-crossed-product-subrings-have-local-annihilation
kind: claim
title: A unital subring of C(X,k) ⋊ Γ containing every clopen indicator has local annihilation, for Γ acting on an infinite compact totally disconnected space
distinct_from:
  steinberg-algebras-have-local-annihilation: that is the Steinberg algebra A_k(G) of an ample groupoid, whose elements are finite combinations of χ_B; this allows arbitrary continuous coefficient functions (for example the harmonic function of the SL_3(Z) Toeplitz ring), which are not locally constant, as long as the subring contains all clopen indicators.
  local-annihilation-makes-projective-el-simple: that is the criterion that consumes local annihilation; this supplies it for crossed-product-type subrings.
artifacts:
  - research/artifacts/gq-referee-b-sl3-toeplitz-harmonic-pe-groups-are-simple.md
  - research/artifacts/gq-referee-c-sl3-toeplitz-harmonic-pe-groups-are-simple.md
---

**ESTABLISHED** by `clopen-crossed-product-subrings-have-local-annihilation-proof` (elementary: the
Steinberg-algebra argument with the coefficient functions allowed to be arbitrary). Referees
`gq-referee-b` and `gq-referee-c` PASS (reports `gq-referee-b-` and
`gq-referee-c-sl3-toeplitz-harmonic-pe-groups-are-simple.md` in `research/artifacts/`; C re-derived Steps 1–3).
The additive-span form proved here is stronger than the Lean predicate `LocalAnnihilation`.

## Statement

- Let `X` be an infinite compact Hausdorff totally disconnected space.
- Let `k` be a commutative ring and `C(X, k)` a ring of `k`-valued functions on `X` under
  pointwise operations. The topology on `k` does not matter; all that is needed is that `C(X, k)`
  is a commutative ring of functions containing the indicators `χ_V` of clopens `V`.
- Let a group `Γ` act on `X` by homeomorphisms and preserve `C(X, k)`. Form the algebraic crossed
  product `C(X, k) ⋊ Γ`, with elements `Σ_γ g_γ u_γ` (finite sums) and multiplication rule
  `u_γ g u_γ^-1 = g ∘ γ^-1`.
- Let `R` be a unital subring of `C(X, k) ⋊ Γ` containing `χ_V` for every clopen `V ⊆ X`.

Then `R` has local annihilation, in the sense of `local-annihilation-makes-projective-el-simple`:
- for every finite `F ⊆ R`, the elements `s ∈ R` admitting `t ∈ R \ {0}` with `ts = 0` and
  `tfs = 0` for all `f ∈ F` generate `R`;
- in fact there is a clopen partition `V_1, ..., V_r` of `X` with `χ_(V_i) R` inside that set for
  every `i`.

## Consequence

If such an `R` is also a simple ring, then for `n >= 3` every normal subgroup of `E_n(R)` is
central or everything, and `E_n(R)/Z(E_n(R))` is simple, by
`local-annihilation-makes-projective-el-simple`.

This applies to the SL_3(Z) Toeplitz harmonic ring (`sl3-toeplitz-harmonic-pe-groups-are-simple`).
It also applies to every harmonic crossed-product ring on main that contains `LC(X, Z)`.
