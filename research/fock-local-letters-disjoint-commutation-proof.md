---
rg: 2
id: fock-local-letters-disjoint-commutation-proof
kind: route
title: Asymptotically free actions on one Fock factor give local intertwiners, and operators on different tensor factors commute exactly
target: fock-local-letters-extend-level-models-with-disjoint-commutation
requires:
  - exterior-tensor-powers-are-asymptotically-free
artifacts:
  - research/artifacts/fock-local-rank-models-2026-09-12.md
---

Section 2 of the artifact: Definition 2.1, Theorem 2.2, Remark 2.3, Consequence 2.4.

1. **Factorization.** For `A` resolved at depth `j`, the wedge isomorphism gives
   `Λ(U_j) = Λ(U_A^(j)) ⊗ Λ(U_(A^c)^(j))`, compatibly with `Λ(a_A ⊕ a_(A^c)) = Λ(a_A) ⊗ Λ(a_(A^c))`.
2. **Two actions on the `A`-factor.** `a` and `φ_g(a)`, for `a ∈ Γ_i = B_g^A ∩ L_i`, act on the `A`-factor.
   Both are exterior tensor powers of faithful modules of the same quotient of `Γ_i`, so they are free
   up to vanishing proportion.
3. **Local intertwiner.** Matching free parts gives `X_(g,j)` with rank error `<= δ_(i,j)`. A moving index
   `i(j) -> ∞` puts every `a ∈ B_g^A` in the exhaustion for almost all `j`.
4. **Exact relations.** Level elements supported off `A`, and letters with disjoint supports, act on
   other tensor factors, so they commute with `X_(g,j) ⊗ 1` exactly.
5. **Characteristic three.** `z_A` is central in `Γ_i` and fixed by `φ_g`. Graded matching makes `X` even,
   so the model restricts to `Λ^odd` with `z -> −1`.
