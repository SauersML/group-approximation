---
rg: 2
id: positive-characteristic-surface-linear-proof
kind: route
title: Realize the coefficient ring in L_p ⊗ L_p and avoid the scalar centre with diag(x, 1)
target: positive-char-surface-linear-groups-satisfy-boone-higman
requires:
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - char-two-surface-linear-groups-satisfy-boone-higman
  - char-two-laurent-linear-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/boone-higman-prime-field-leavitt-hosts-2026-09-12.md
---

This is artifact Theorem 6.1. Let `H <= GL_n(K)` be finitely generated.

1. **Reduction.** Follow `char-two-surface-linear-groups-proof` with `F_p` in
   place of `F_2`.
   - The regular representation and cleared denominators give
     `H <= GL_(nm)(F_p[t_1, ..., t_d][1/h])` with `d <= 2`.
   - Divide by the leading coefficient to make each localizing polynomial monic
     over the localized base.
2. **The Laurent step.** `char-two-laurent-linear-groups-proof` supplies the
   Thompson unit `g`. The same test-module argument, over `F_p`, shows that
   `F_p[g^±] -> L_p` is injective, since the vectors `g^k(v)` are distinct basis
   vectors.
3. **Into the tensor square.** As in the characteristic-two proof, the
   coefficient ring embeds unitally in `L_p ⊗ L_p`, so
   `H <= GL_N(L_p ⊗ L_p) ≅ (L_p ⊗ L_p)^x`.
4. **Avoiding the centre.** Compose with `x |-> diag(x, 1)` in
   `M_2(L_p ⊗ L_p) ≅ L_p ⊗ L_p`. This is scalar only for `x = 1`, so `H` embeds
   in `(L_p ⊗ L_p)^x / F_p^x`.
5. **Conclusion.** `odd-leavitt-unit-groups-mod-scalars-are-fp-simple` makes
   that quotient finitely presented and simple.
