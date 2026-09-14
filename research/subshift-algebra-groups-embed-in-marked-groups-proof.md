---
rg: 2
id: subshift-algebra-groups-embed-in-marked-groups-proof
kind: route
title: Cylinder-root words and a window bound give both moduli, and forbidden windows force containment
target: subshift-algebra-groups-embed-in-marked-groups
requires: []
artifacts:
  - research/artifacts/sk-fp-sofic-b-z2-soficity-map-2026-09-13.md
---

Direct proof, written in full in the artifact §§2–3.

- **Cylinder words.** `χ_[p] = ∏_(δ ∈ F) u_δ χ_(p(δ)) u_δ^(-1)` is a product of at most `|F|(2ρ+1)` marking
  coefficients. Nested commutators `e_ij(s_1 ⋯ s_l) = [e_ik(s_1), e_kj(s_2 ⋯ s_l)]` turn it into a word
  `W_p` of length `3·2^(l-1) - 2`. If `e_12(r)` is a scalar matrix, then `r = 0`. And `χ_[p] = 0` on `Y` iff
  `p ∉ L(Y)`.
- **Window bound.** Every `Y` is a quotient of the full shift, and `R_(A^Γ) → R_Y` has kernel
  `{Σ f_γ u_γ : f_γ|_Y = 0}`. A word of length `<= r` evaluates to a matrix whose entries (minus a constant
  scalar) are `Σ_(|γ|<=r) f_γ u_γ`, with each `f_γ` a function of the `B(r)`-pattern.
- **Embedding.**
  - Injectivity comes from the cylinder words.
  - Continuity comes from the window bound.
  - Inverse continuity comes from the length bound on `W_p`.
  - The image is closed by compactness.
  - Containment comes from restriction maps and from the cylinder words.
- **Isolation.**
  - An SFT window `K` with `L_K(Y) = L_K(Ω)` forces `Y ⊆ Ω`, and then `Y = Ω` by minimality.
  - A minimal subshift not of finite type is the limit of its finite-type approximations
    `X^(F) = {y : (γ·y)|_F ∈ L_F(X) for all γ} ≠ X`.
- **Finite subshifts.**
  - `LC(Γ/H,F_q) ⋊ Γ ≅ M_([Γ:H])(F_q[H])`. For `Γ = Z^d` this makes `G_Y` a finitely generated linear group over
    a commutative domain, hence residually finite (Mal'cev).
  - For `Γ = Z`, the periodic word with the same `(2k+1)`-words gives the approximating finite subshifts.
