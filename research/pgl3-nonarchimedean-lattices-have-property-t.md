---
rg: 2
id: pgl3-nonarchimedean-lattices-have-property-t
kind: claim
title: Every lattice in PGL_3(K), for a nonarchimedean local field K of characteristic zero, has property (T)
distinct_from:
  affine-semidirect-sl3-source-has-property-t: that is the integral affine group Z^3 x| SL_3(Z) through a real Lie group; this is lattices in the p-adic group PGL_3(K), passing through the open image of SL_3(K).
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that is a central extension over a real Lie group; this is a nonarchimedean adjoint group and uses no central extension theorem.
---

**ESTABLISHED (import plus a three-line derivation)** through
`pgl3-nonarchimedean-lattices-property-t-citation`.

## Statement

Let `K` be a nonarchimedean local field of characteristic zero and `Γ` a lattice in
`G = PGL_3(K)`. Then `Γ`, as a discrete group, has property (T).

## Derivation from the imported theorems

- `SL_3(K)` has (T) (BdHV Theorem 1.4.15, quoted in the route).
- Let `H` be the image of `SL_3(K)` in `G`. The map `SL_3(K) -> H` is a continuous
  surjective homomorphism, so `H` has (T) (BdHV Theorem 1.3.4).
- `H` is the kernel of the continuous homomorphism `G -> K^*/(K^*)^3`, `[g] ↦ det g`.
  This map is well defined because scalars have cube determinants. The kernel is exactly
  `H`: if `det g = μ^3`, then `μ^{-1} g ∈ SL_3(K)`.
- `(K^*)^3` is an open subgroup of `K^*`:
  - In characteristic zero, `3` is a unit or has finite valuation, so Hensel's lemma
    makes `x ↦ x^3` cover a neighbourhood of `1`.
  - `K^* ≅ Z × O^*` with `O^*` compact. So `K^*/(K^*)^3` is finite and discrete.
- Hence `H` is an open, closed, finite-index normal subgroup of `G`. The counting
  measure on `G/H` is a finite invariant regular Borel measure, so `G` has (T) (BdHV
  Theorem 1.7.1, (ii) ⇒ (i)).
- `Γ` is a lattice in `G`, so `Γ` has (T) (BdHV Theorem 1.7.1, last sentence).
