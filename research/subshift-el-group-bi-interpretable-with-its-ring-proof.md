---
rg: 2
id: subshift-el-group-bi-interpretable-with-its-ring-proof
kind: route
title: Bounded elementary generation makes EL_3 existentially definable in the ring, and reading the matrix off any 78-term factorisation gives a definable isomorphism onto the doubly interpreted copy
target: subshift-el-group-bi-interpretable-with-its-ring
requires:
  - subshift-el-group-interprets-its-crossed-product-ring
  - subshift-el-groups-boundedly-elementary-generated
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

Full argument in the artifact §5.

- **`G` in `R`.** Interpret `M_3(R)` as `R^9`. Bounded elementary generation with a fixed position pattern turns `G = e_{i_1j_1}(R)⋯e_{i_78j_78}(R)` into an existential formula with 78 ring variables, so `G` is a definable subgroup of `GL_3(R)` and its group law is the definable matrix product.
- **Ring-side composite.** `R → G^{(R)} → R^{**}` is `r ↦ ê_13(r) ↦ r`, whose graph is definable in `R`.
- **Group-side composite.** With `R^*` the interpreted ring of the target's first requirement and `G^*` the copy of `G` interpreted inside `R^*`, put

      Θ(g,M) :⟺ ∃ a_1 … a_78 ∈ U_13 [ g = ∏_k w_{i_kj_k} a_k w_{i_kj_k}^{-1} ∧ M = ∏_k ê_{i_kj_k}(a_k) ].

  - **Definable** in `G`, with the parameters of the first requirement together with the permutation parameters `w_{ij}`.
  - **Total**: the bound writes `g = ∏_k e_{i_kj_k}(r_k)`; take `a_k = e_13(r_k)`.
  - **Single-valued**: under the isomorphism `R^* ≅ R`, the second product is the matrix `∏_k e_{i_kj_k}(r_k) = g`, so `M` does not depend on the chosen factorisation.
  - **Injective**: elements of `G` are matrices, so `g` is recovered from `M`.
  - **Surjective and multiplicative**: apply the bound to elements of `G^*` and to `gh`.
- So `Θ` is a definable isomorphism `G → G^*`, and with the ring-side composite the pair is bi-interpretable with parameters.

**Failure mode without the bound.** For a general ring, `E_3(R)` is the increasing union of the sets of `n`-fold products of elementary matrices. No single formula defines it, `Θ` has no fixed arity, and the argument collapses. The hypotheses of the bounded generation claim (minimal Cantor system, `F_2`, rank 3) are therefore inherited verbatim.
