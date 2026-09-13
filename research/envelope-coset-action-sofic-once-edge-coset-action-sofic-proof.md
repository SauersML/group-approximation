---
rg: 2
id: envelope-coset-action-sofic-once-edge-coset-action-sofic-proof
kind: route
title: Separate the graph by finite quotients, drop the finite factor, embed the orbits in a product
target: envelope-coset-action-sofic-once-edge-coset-action-sofic
requires:
  - twisted-rope-is-a-central-rope-over-an-rf-envelope
  - finite-commuting-extension-of-a-sofic-action-is-sofic
  - separating-sofic-quotient-sets-make-an-action-sofic
  - gkp-sofic-action-toolkit
  - three-bridge-is-cyclic-fiber-product-with-finite-cep
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13-part2.md
---

The full derivation, steps (i)--(viii), is Section 2 of
`research/artifacts/twisted-rope-rf-envelope-2026-09-13-part2.md`.

- **(i)--(ii) Separation.** `R-hat` is residually finite, so the graphs
  `C_n` decrease with intersection `C_e`. The equivariant maps
  `D_e/C_e -> D_e/C_n` separate any finite set for large `n`. Then (S1)
  applies.
- **(iii) Quotient.** `1 x ker phi_n` is normal in `D_e` and lies in `C_n`,
  so the action factors through `Gamma_e x Phi_n`. Composition with a
  quotient map preserves soficity, with the same charts.
- **(iv) Finite factor.** [[finite-commuting-extension-of-a-sofic-action-is-sofic]]
  drops `Phi_n`.
- **(v) Orbits.** As a `Gamma_e`-set, the coset space is a finite union of
  copies of `Gamma_e/S''_n`, with `S''_n = S_e ∩ Lambda^-1(M_n)`. Then GKP
  Proposition 2.16 applies ([[gkp-sofic-action-toolkit]]).
- **(vi) Embedding.** `g S''_n |-> (g S_e, Lambda(g) M_n)` is equivariant and
  injective.
- **(vii) Product.** (S2) applies, and then GKP Proposition 2.15(3)
  restricts to the diagonal `Gamma_e`.
- **(viii) Separability.** `Lambda` is onto `G-hat`. `M_n` is an
  intersection of finite-index subgroups: `H x H` is the kernel of
  `chi x chi` onto `Z^2`, (BCF2) extends the finite quotients of `H` to `P`,
  and the modular law gives `M_n W ∩ (H x H) = M_n`. So (C1) applies.
