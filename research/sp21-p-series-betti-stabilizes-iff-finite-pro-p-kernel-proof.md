---
rg: 2
id: sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel-proof
kind: route
title: Completions of the derived p-series are the Frattini series; equal Frattini quotients push the kernel down the series to the trivial intersection
target: sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel
requires: []
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**Imported inputs.**
- **(DDMS)** For uniform `U` of dimension `D`: `Φ^i(U) = U^(p^i)` is uniform of
  dimension `D`, so `d(U^(p^i)) = D`. Every compact p-adic analytic group has an
  open normal uniform subgroup (also stated in Ardakov–Brown arXiv:math/0511345
  §2, read from the PDF).
- **(C)** The pro-p completion of a normal subgroup of p-power index is its
  closure in the pro-p completion. The closure of the derived p-series is the
  Frattini series.
- **(T)** Kazhdan's property (T) holds for finite-index subgroups of `Γ`.

Write `P = Δ̂_p`, `π: P ->> U`, `N = ker π` and `N_i = N ∩ Φ^i(P)`. By (C),
`d_p(D_i) = d(Φ^i(P))`, and `π(Φ^i(P)) = U^(p^i)`.

1. **Lower bound.** `Φ^i(P) ->> U^(p^i)` gives `d(Φ^i(P)) >= D`.
2. **Finite `N` gives equality.** `N_i` decreases, is finite, and has trivial
   intersection, so `N_i = 1` for large `i`. Then `Φ^i(P) ≅ U^(p^i)`, and
   `d_p(D_i) = D`.
3. **Equality gives finite `N`.**
   - If `d(Φ^i(P)) = D`, the induced map `Φ^i(P)/Φ^(i+1)(P) -> U^(p^i)/U^(p^(i+1))`
     is a surjection between `F_p`-spaces of equal dimension, hence an
     isomorphism.
   - So `π^(-1)(U^(p^(i+1))) ∩ Φ^i(P) = Φ^(i+1)(P)`, which contains `N_i`. Hence
     `N_i = N_(i+1)`.
   - If this holds for all `i >= i_0`, then `N_(i_0) = ∩_i N_i = 1`, and `N` embeds
     in the finite group `P/Φ^(i_0)(P)`.
4. **Infinite `N`.** By step 3, equality fails at infinitely many levels. With
   step 1, `d_p(D_i) > D` there. ∎
