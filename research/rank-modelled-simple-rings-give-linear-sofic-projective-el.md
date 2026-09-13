---
rg: 2
id: rank-modelled-simple-rings-give-linear-sofic-projective-el
kind: claim
title: If a simple algebra over a finite field has a unital rank model, its elementary groups modulo scalars are linear sofic over that field
distinct_from:
  leavitt-el3-rank-models-over-finite-fields-are-trivial: that asks whether EL_3 over a Leavitt algebra has any nontrivial rank model; this builds rank models of EL_m and of its scalar quotient from a ring-level rank model, which the Leavitt algebra lacks.
  el3-rank-models-factor-through-ring-rank-models: that is the converse direction, from group models to ring models, for rings without a ring model; this is the forward direction, from ring models to group models.
artifacts:
  - research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a finite field, `R` a simple unital `k`-algebra with
centre `k`, and `Psi : R -> M` a unital homomorphism into a rank ultraproduct of matrix algebras
over `k`. For `m >= 2`, put `G = EL_m(R)` and `Z = G ∩ k^x 1_m`. Then `G` and `S = G/Z` embed in
rank ultraproducts of general linear groups over `k`. That is, they are `k`-linear sofic in the
ultraproduct sense of Arzhantseva–Păunescu.

**Mechanism.**
- **Faithfulness.** `Psi` is injective because `R` is simple.
- **Scalar quotient.** `S` is modelled through the adjoint `A -> A ⊗ A^(-T)`. This is an exact
  homomorphism with rank defect `rk(Ad A - Ad B) <= 2N rk(A - B)`, and it kills scalars.
- **Separation.** `N^2 - dim C(A) >= N min_λ rk(A - λ)`, where `C(A)` is the commutant, by the
  Jordan-partition count of `dim C(A)`. Faithfulness bounds `rk(A - λ)` below for `λ ∈ k`, and
  Galois symmetry does so for `λ ∉ k`.

**What it does not give.** Soficity. Upgrading is Arzhantseva–Păunescu Question 8.5 at `S`, and
no conversion from rank defects to Hamming defects is known.

**For the ring route.** With `free-minimal-crossed-products-are-simple-with-rank-models`, every
free minimal `Z^d` crossed product gives an infinite `k`-linear sofic group `S`, Kazhdan for
`m >= 3`. If the ring is finitely presented and `S` is finitely presented and simple, `S` is a
finitely presented infinite simple Kazhdan linear sofic group.

Route: `rank-modelled-simple-rings-give-linear-sofic-projective-el-proof`.
