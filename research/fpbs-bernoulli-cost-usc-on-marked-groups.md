---
rg: 2
id: fpbs-bernoulli-cost-usc-on-marked-groups
kind: claim
title: Bernoulli cost is upper semicontinuous on the space of marked groups
distinct_from:
  burton-kechris-cost-usc-and-maximum-action: that is upper semicontinuity of cost in the weak topology on actions of one fixed group; this varies the group in the Chabauty topology on marked groups and compares Bernoulli shifts of different groups
  fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap: that compares Bernoulli cost with ultraproduct cost for one group; this is a semicontinuity statement across a convergent sequence of marked groups
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**ESTABLISHED.** Let `G_n -> G` in the space of `k`-marked groups. Then
`limsup_n C(b_(G_n)) <= C(b_G)`. For finite `G_n`, `C(b_(G_n))` means `1 - 1/|G_n|`.

The key device is a finite certificate: a finite window, an interval partition, finitely many word-labelled cylinder
pieces, and a route radius `rho`. Generator edges are added on the set where `x` and `s x` are not joined within
`rho` steps. The result always generates, and its cost is a function of `N cap B_(R(Z))` alone. Such certificates
compute `C(b_G)` as an infimum, and they transfer verbatim to every `G_n` that agrees with `G` on `B_(R(Z))`.

This is the cost analogue of Pichot's semicontinuity of `beta_1`. Artifact, Section 1.
