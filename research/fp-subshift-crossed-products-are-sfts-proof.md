---
rg: 2
id: fp-subshift-crossed-products-are-sfts-proof
kind: route
title: A diagonal representation on locally admissible configurations detects every forbidden pattern
target: fp-subshift-crossed-products-are-sfts
requires: []
artifacts:
  - research/artifacts/free-minimal-subshift-elementary-groups-2026-09-13.md
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

This is Proposition B of the part 3 artifact, using Lemma 1 of the part 1 artifact.

1. **Normal form.** Lemma 1 of part 1 uses only that `X` is a subshift. Every relation of `R_X` of
   word length `<= D` holds in `A_D`, and `A_D` is finitely presented. So finite presentation of
   `R_X` gives `A_D -> R_X` an isomorphism for some `D`.
2. **The diagonal model.** On finitely supported functions `Z^2 -> ℓ(Y_D)`, with
   `Y_D = {y : every B_D-pattern of y occurs in X}`, let `e_a` act at site `w` by multiplication by
   `[y(w) = a]`, and let `u^g` translate. All site operators are diagonal, so (R2) and (R3) hold.
   (R4) holds because `y ∈ Y_D`.
3. **Descent.** Through `A_D = R_X`, the pattern idempotent `p_π` of every pattern `π` not occurring
   in `X` acts by zero. So no `y ∈ Y_D` contains `π`, and `Y_D ⊆ X`.
4. **Conclusion.** `X ⊆ Y_D` is clear, so `X = Y_D`, which is defined by forbidding finitely many
   `D`-ball patterns.
