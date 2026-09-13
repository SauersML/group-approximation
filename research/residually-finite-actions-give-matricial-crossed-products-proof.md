---
rg: 2
id: residually-finite-actions-give-matricial-crossed-products-proof
kind: route
title: Genuine finite Gamma-sets that approximately follow the action are exact local ring models
target: residually-finite-actions-give-matricial-crossed-products
requires: [simple-rings-with-local-matrix-models-are-matricial, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part1.md
---

Artifact part 1, §2.
- **Simplicity.** For `0 != P ∈ J`, arrange `f_e != 0`. Pick a free point `x` with `f_e(x) = c != 0`
  and a clopen `W ∋ x` with `α(g)W ∩ W = ∅` for `g ∈ supp P \ {e}`. Then `χ_W P χ_W = c χ_W`, so
  `χ_W ∈ J`. Minimality covers `X` by translates, and inclusion–exclusion gives `1 ∈ J`.
- **Models.** For `(F_n, ε_n)`, take the Kerr–Nowak model `(E_n, β_n)` and put
  `ψ_n(Σ f_g u_g) = Σ D_n(f_g) P_n(g)`.
- **Exact on windows.** On basis vectors, `ψ_n(f u_g) ψ_n(f' u_h)` and `ψ_n(f (f'∘α(g)^(-1)) u_(gh))`
  differ only in `f'(β(g^(-1)) w)` against `f'(α(g^(-1)) w)`. These agree once `g^(-1) ∈ F_n` and `f'`
  is constant on `ε_n`-small sets, since `β` is a genuine action.
- **Embedding.** The windows exhaust `R`, so the lemma
  `simple-rings-with-local-matrix-models-are-matricial` gives the injective embedding.
- **Item 3.** `GL_m(R)` embeds in `∏_ω GL_(m N_n)(F_q)`, an ultraproduct of finite groups.
