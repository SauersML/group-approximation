---
rg: 2
id: pauli-tower-sections-are-somewhere-scalar-proof
kind: route
title: The adjoint top Stiefel–Whitney class of a Pauli tail is the Moore determinant, and it survives on the base
target: pauli-tower-sections-are-somewhere-scalar
requires: []
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

Complete direct proof, Sections 1–3 of the artifact. Review PASS (part 9 §9.2 of
`research/artifacts/ex-review2-analysis-2026-09-13-part9.md`), which re-derives Proposition D as well.

1. **Characters (Lemma 1).** `Ad X` negates `Y, Z`; `Ad Z` negates `X, Y`. So `X, Y, Z` carry the
   characters `(0,1), (1,1), (1,0)` of `(Z/2)²`. For `r` tensor factors the Pauli strings form an
   `R`-basis of the self-adjoint matrices, and `a ↦ χ_a` is a bijection from strings onto
   `Hom((Z/2)^{2r}, F_2)`, with the identity string the only one with trivial character.
2. **Splitting.** The traceless self-adjoint bundle `E` of `B_{n,m}` is associated to the principal
   bundle `Π_{n<k≤m} (S^{d_{2k−1}} × S^{d_{2k}})` through this representation, so
   `E = ⊕_{χ≠0} λ_χ`.
3. **First classes.** `λ_χ = ⊠_j γ_j^{c_j}` for `χ = (c_j)`, with `γ_j` the tautological line bundle
   of `RP^{d_j}`. So `w_1(λ_χ) = Σ_j c_j t_j`.
4. **Top class.** Whitney: `w_{top}(E) = Π_{0≠c} (c·t)`.
5. **Moore (Lemma 2).** Over `F_2` this product equals `det[t_j^{2^i}] = Σ_σ Π_j t_j^{2^{σ(j)}}`. Each
   nonzero form divides the determinant, since Frobenius is additive. The degrees agree, and the
   determinant is nonzero because distinct `σ` give distinct monomials.
6. **Survival.** Künneth gives `H*(Z_{n,m}; F_2) = F_2[t_j]/(t_j^{d_j+1})`. The bijection
   `σ(j) = j − 2n − 1` on `j ∈ {2n+1, ..., 2m}` has exponents `2^{j−2n−1} ≤ 2^{j−1} = d_j`. So
   `w_top(E) ≠ 0`.
7. **Conclusion.** `h − tr(h)·1` is a continuous section of `E`. If it never vanished, `E = E' ⊕ R`
   and `w_top(E) = 0`. So `h` is scalar somewhere.
8. **Vector bundles (Proposition D).** `e(Herm_0 End W)` is pulled back from `H^{w²−1}(BU(w); Z)`.
   It is zero in odd degree, and for odd `w` it restricts to zero on `BT` (trivial summand
   `Lie(T) ∩ su(w)`), where restriction is injective. Its mod-2 reduction is `w_top`.
