---
rg: 2
id: fjc-crossed-products-of-k-trivial-regular-rings-vanish-proof
kind: route
title: Assemble K of the crossed product from the trivial subgroup and skew Laurent rings over infinite cyclic subgroups, all K-trivial
target: fjc-crossed-products-of-k-trivial-regular-rings-vanish
requires:
  - crossed-product-rings-inherit-fjc-with-additive-coefficients
  - regular-coherent-laurent-coefficients-kill-twisted-nil-terms
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

Put `A = R_(α,τ)P` and let `𝒜 = A_(α,τ)` be the additive `P`-category of
`crossed-product-rings-inherit-fjc-with-additive-coefficients`. Full proofs are
in Sections 2 and 3 of the artifact.

1. **Assembly.** By part 2 of the import, `H_n^P(E_VCyc P; K_𝒜) -> K_n(A)` is
   bijective for every `n`.
2. **The family.** `P` is torsion-free, so each virtually cyclic subgroup is
   trivial or infinite cyclic. This standard fact was not re-derived.
3. **The trivial subgroup (artifact Lemma 2.1).** Put `c = τ_(e,e)`. Then `c` is
   central, `τ_(e,k) = c`, `τ_(g,e) = α_g(c)` and `1_A = c^−1 e`. The map
   `r |-> r c^−1 e` is a ring isomorphism `R -> A_e = R e`. So
   `H_n^P(P/1; K_𝒜) ≅ K_n(A_e) = 0`, by part 1 of the import.
4. **Infinite cyclic subgroups (artifact Lemma 2.2).** Let `H = <g> ≅ Z` and
   `t = 1·g`. The ring `A_H = ⊕_n R g^n` is `Z`-graded with degree-zero part
   `A_e`.
   - `t` is a unit, and `t^n ∈ R^x g^n`. Hence `(A_H)_n = A_e t^n`.
   - `φ = Ad(t)` preserves `A_e`.
   - `Σ a_n s^n |-> Σ a_n t^n` is an isomorphism `(A_e)_φ[s, s^−1] -> A_H`.

   Since `A_e ≅ R`, every `A_e[Z^m]` is regular coherent and `K(A_e) ≃ 0`. By
   `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`,
   `K_n(A_H) = 0`. So `H_n^P(P/H; K_𝒜) = 0` by part 1 of the import. The
   opposite Laurent convention is the same ring for `φ^−1`, so the convention of
   the import does not matter.
5. **Skeletal induction.** Take a `P`-CW model `Y` of `E_VCyc P`. By excision
   and the disjoint union axiom, `H_*^P(Y_j, Y_(j−1)) ≅ ⊕_i H_(*−j)^P(P/H_i) = 0`.
   The long exact sequences give `H_*^P(Y_j) = 0` for every `j`, and
   `H_*^P(Y) = colim_j H_*^P(Y_j) = 0`. These are the Davis–Lück properties of a
   `P`-homology theory given by an `Or(P)`-spectrum. They were not re-read, as in
   Step 4 of `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`.
6. **Conclusion.** `K_n(A) ≅ H_n^P(E_VCyc P; K_𝒜) = 0` for every `n`. ∎
