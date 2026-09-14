---
rg: 2
id: car-bernoulli-crossed-product-is-lamplighter-ring
kind: claim
title: The binary lamplighter crossed product LC(2^Z,F_2) ⋊ (Z/2 ≀ Z) is the algebraic Bernoulli crossed product (⊗_Z M_2(F_2)) ⋊ Z of the F_2-CAR algebra
distinct_from:
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that proves EL_n over the lamplighter ring is simple Kazhdan LEF for every LEF acting group Δ; this identifies the Δ = Z ring with the tensor-shift crossed product of the algebraic CAR algebra over F_2.
  uhf-cyclic-shift-has-strict-compressed-commutant: that is about commutants of a cyclic shift on a UHF algebra; this is an algebraic ring isomorphism.
artifacts:
  - research/artifacts/sk-strong-5-second-family-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `L = Z/2 ≀ Z` act on `2^Z`: `s` is the shift and `a` flips the coordinate `0`.
Let `B = ⋃_n ⊗_{t∈[−n,n]} M_2(F_2)` be the algebraic infinite tensor product, with inclusions `x ↦ 1 ⊗ x ⊗ 1`
and tensor shift `σ`. Then

`LC(2^Z, F_2) ⋊ L ≅ B ⋊_σ Z`,

and every element has a unique normal form `Σ_j b_j s^j` with `b_j ∈ B`.

So `G_CAR = EL_3(B ⋊_σ Z)` is the case `Δ = Z` of `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`: it is
infinite, finitely generated, simple and Kazhdan, with trivial centre.

Credit: folklore. The C*-analogue, `C(2^Z) ⋊ ⊕_Z Z/2 ≅` the CAR algebra with the Bernoulli shift, is standard. The
novelty check was a grep of main only.

Route: `car-bernoulli-crossed-product-is-lamplighter-ring-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS; every step re-derived (see the artifact).
