---
rg: 2
id: fpbs-kazhdan-no-rapid-descent
kind: claim
title: No Kazhdan group has an abelian p-series with rapid descent, so every Kazhdan group has zero p-gradient
distinct_from:
  fpbs-power-p-deficiency-excludes-property-t: that excludes (T) under positive power p-deficiency; this excludes (T) under the strictly weaker hypothesis of a rapidly descending abelian p-series, which positive power p-deficiency implies via fpbs-power-p-deficiency-schreier-bound.
  fpbs-lackenby-rapid-descent-p-large: that is the finitely presented theorem; this holds for all Kazhdan groups, including infinitely presented ones.
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

**ESTABLISHED (written deduction).** Let `Gamma` be a group with property (T)
and `p` a prime. Then `Gamma` has no chain
`Gamma = Gamma_1 > Gamma_2 > ...` with `Gamma_(i+1)` normal in `Gamma_i`,
`Gamma_i/Gamma_(i+1)` elementary abelian, and
`inf_i d_p(Gamma_i/Gamma_(i+1))/[Gamma:Gamma_i] > 0`.

Consequently, every finite index `L` in `Gamma` has `p`-gradient zero:
`inf (d_p(H)-1)/[L:H] = 0` over subnormal `H` of `p`-power index. Also,
`d_p(H)/[Gamma:H]` is not bounded below along any family of subnormal
`p`-power index subgroups that is cofinal in the pro-`p` topology.

Use downstream: the `p`-gradient, power-deficiency, derived `p`-series and
pro-`p`-cofinal certificates for `fpbs-kazhdan-positive-rank-gradient` are
dead, for finitely and infinitely presented Kazhdan groups alike.
