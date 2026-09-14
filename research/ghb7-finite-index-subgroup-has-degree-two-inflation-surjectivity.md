---
rg: 2
id: ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity
kind: claim
title: Some finite-index subgroup of GHB_2(7) with positive second Betti number has every degree-two finite cyclic class inflated from a finite quotient
distinct_from:
  every-hyperbolic-group-is-good: that is goodness in Serre's sense for all hyperbolic groups, all finite modules and all degrees; this is only degree two, trivial cyclic coefficients, surjectivity, for one finite-index subgroup of GHB_2(7)
  ghb7-finite-index-z-extension-center-survives: that is survival of the centre of one central Z-extension at unbounded orders; this is the profinite-cohomological property that forces survival at every order for every central Z-extension
---

**OPEN.** There is a finite-index subgroup `K <= G = G_{HB_2}(7)` with `b_2(K;Q) >= 1` such that,
for every `n >= 1`, every class in `H^2(K;Z/n)` is inflated from a finite quotient of `K` (property
(G2) of `degree-two-inflation-onto-makes-z-extension-centres-survive`).

**Candidates.** `K_7 = Ker(G → Z/7, a,b,c ↦ 1)` with `b_2 = 6`, the abelianization kernel with
`b_2 = 216`, and every torsion-free finite-index subgroup (`ghb7-normal-subgroup-b2-is-orbit-euler-count`).

**Consequence.** Through route `ghb7-centre-survival-via-degree-two-goodness`, it gives
`ghb7-finite-index-z-extension-center-survives`, hence `ghb7-is-not-flexibly-hs-stable`. So flexible
HS stability of `G` forces every finite-index subgroup with `b_2 >= 1` to fail (G2) at some `n`.

**Calibration.** `G` is hyperbolic and Kazhdan, not cubulated, so Kropholler–Wilkes goodness for
virtually special groups does not apply (Attempts of `every-hyperbolic-group-is-good`). No goodness
theorem for hyperbolic Kazhdan groups is recorded on main.

ROUTES
ghb7-degree-two-inflation-via-hyperbolic-goodness
