---
rg: 2
id: leavitt-annulus-north-south-units-have-cyclic-centralizers-proof
kind: route
title: Clean germs replace point dynamics, measure forces flow invariance, and aligned terms read the polynomial
target: leavitt-annulus-north-south-units-have-cyclic-centralizers
requires: [leavitt-algebras-l-k-1-n-are-simple]
artifacts:
  - research/artifacts/leavitt-annulus-north-south-centralizer-2026-09-13.md
---

The full proof is in `research/artifacts/leavitt-annulus-north-south-centralizer-2026-09-13.md`, Sections 1–4.
Write `p = ζγ^∞`, `q = ξδ^∞`, and `M_flow = ⊕_k M_(D_k)` for the functions vanishing near `p` and `q`.

1. **Annuli move.** The defining identities give `u 1_(D_k) u^(-1) = 1_(D_(k+1))` for all `k`, together with
   `t_ζ u^(-j) = t_(ζγ^j)` and `t_ξ u^j = t_(ξδ^j)` for `j >= 0`.
2. **Flow invariance.** Let `g` commute with `u^a`. If `g f`, with `f ∈ M_flow`, does not vanish near `p`, then
   `u^(-am) g f = 1` on `[ζ]`. But `g u^(-am) f` is supported with measure tending to `0`, by the support bound
   for `g`. Near `q` use `u^(am)`.
3. **Coefficients.** For `f_0 ∈ M_(D_0)` and large `n`, `g u^n f_0 = Σ_d ε_d u^(n+d) f_0`.
   - Aligned terms `(α, β)`, those with `α σ^|β|(p) = p`, contribute `u^(n+d)f_0`.
   - The other terms land off `[ζγ^c]`, where by step 2 the total vanishes.
   - So `g = p_g(u)` on `M_flow`.
4. **Globalize.** An element killing `M_flow` kills every aperiodic Chen module, so it is `0` by simplicity.
   So `g = p_g(u)`. `M_flow` is free over `F_2[t^(±1)]` with `t = u`, and the units are monomials. ∎
