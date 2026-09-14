---
rg: 2
id: cantor-crossed-product-idempotents-similar-to-clopen-ones-proof
kind: route
title: Split the idempotent at every tower cut by a Laplace-chosen coordinate transversal, conjugate by the canonical intertwiner, and diagonalize in the tower algebra
target: cantor-crossed-product-idempotents-similar-to-clopen-ones
requires: []
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md
---

Full derivation: `research/artifacts/sk-algebraic-putnam-2026-09-13-part2.md` §2–§3. Summary of the steps, with the checks:

- **Setting.** Orbit representation `V = F^{(Z)}` (faithful). `e` and `1−e` have propagation `≤ w`. `V_− = span{δ_t : t<c}`, `V_+ = span{δ_t : t≥c}`. `E = eV`, `E′ = (1−e)V`, `E_± = E∩V_±`, `E′_± = E′∩V_±`, `Σ = E_−+E′_−+E_++E′_+`.
- **(a) Σ is direct and has finite codimension.** For `|t−c| ≥ w`, `δ_t = eδ_t+(1−e)δ_t` splits on one side. So `V_± = E_±⊕E′_±⊕M_±` with `M_±` spanned by coordinates in `[c−w,c)` and `[c,c+w)`. Directness uses `E∩E′ = 0` and `V_−∩V_+ = 0`.
- **(b) Locality.** A window vector `m` lies in `Σ` iff `eP_±m ∈ V_±`, and then its components are `eP_±m` and `(1−e)P_±m`. So all choices depend on the entries of `e` in a bounded window.
- **(c) `M = Ĩ ⊕ Ĩ′`.** `Ĩ` and `Ĩ′` are the images of `E` and `E′` in `V/Σ ≅ M`. They span because `E+E′ = V`. They are independent: `ξ−η ∈ Σ` with `ξ∈E`, `η∈E′` forces `ξ∈Σ` via `E∩E′ = 0`.
- **(d) Laplace.** `[pr′(B); pr(B)]` is invertible, where `B` is the coordinate basis of `M = M_−⊕M_+` and `pr′, pr` project onto `Ĩ` along `Ĩ′` and onto `Ĩ′` along `Ĩ`. The Laplace expansion along the first `dim Ĩ` rows yields a subset `T` with `pr′(T)` a basis of `Ĩ` and `pr(B∖T)` a basis of `Ĩ′`. So `S = span T` and `S′ = span(B∖T)` satisfy `S⊕S′ = M`, `S⊕Ĩ′ = M`, `S′⊕Ĩ = M`, and both split along `M_−⊕M_+`.
- **(e) Split idempotent.** `e_c` = projection onto `E_−⊕E_+⊕S` along `E′_−⊕E′_+⊕S′`. It agrees with `e` on `Σ`, and its range and kernel split along `V_−⊕V_+`. `Δ_c = e_c − e` is supported in the window with local entries.
- **(f) Intertwiner.** `h_c = e_ce+(1−e_c)(1−e) = 1+Δ_c(2e−1)` satisfies `h_ce = e_ch_c`. It maps `E → range e_c` bijectively (identity on `E_±`; `Ĩ → S` along `S′`, bijective since `S′⊕Ĩ = M`), and `E′ → ker e_c` bijectively (since `S⊕Ĩ′ = M`). So it is invertible, with a window-local inverse.
- **(g) All cuts.** Heights `> 4w+2`; choices per local type (finitely many). `e″ = e+Σ_cΔ_c`:
  - it is idempotent, since the windows are disjoint and `eΔ_c+Δ_ce+Δ_c² = Δ_c`;
  - it splits at every cut, so `e″ ∈ A_𝒫 ≅ ∏_aM_{h_a}(F)` after refining atoms;
  - `h = 1+Σ_cΔ_c(2e−1) ∈ R^×` and `e″ = heh^{−1}`.
- **(h) Tower algebra.** An idempotent of rank `k_a` in `M_{h_a}(F)` is similar to `diag(1^{k_a},0)`. The conjugators per type give `h′ ∈ A_𝒫^×` with `h′e″h′^{−1} = e_W`, `W = ⋃_a⋃_{i<k_a}T^iB_a`.
- **(i) Matrices.** For `M_n(R)`, run the same argument on `V^n` with coordinate bases.

**Model test.** Over `F_2`, `e = e_V+e_Vu` with `V∩TV = ∅` crosses cuts. `(1+e_Vu)e_V(1+e_Vu) = e`, as predicted.
