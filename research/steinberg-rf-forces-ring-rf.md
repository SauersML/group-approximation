---
rg: 2
id: steinberg-rf-forces-ring-rf
kind: claim
artifacts:
  - research/artifacts/gq-referee-a-steinberg-rf-forces-ring-rf.md
  - research/artifacts/gq-referee-b-z-localized-embeds-in-fp-kazhdan-steinberg-group.md
title: For N >= 3 every finite quotient of St_N(R) factors through St_N(F) for a finite quotient ring F of R, so St_N(R) residually finite forces R residually finite
distinct_from:
  steinberg-finite-presentation-and-kazhdan-theorem: that gives finite presentation and property (T) of St_n(R); this concerns its finite quotients.
  resolvent-steinberg-group-is-residually-finite: that asks whether St_N(R_l) is residually finite; this gives the necessary condition that R_l be residually finite.
---

**ESTABLISHED** through `steinberg-rf-forces-ring-rf-proof`. Lane proof; proof-gap review PASS by gq-referee-a and citation review PASS by
gq-referee-b (reports in `artifacts`). Elementary; no
priority is claimed.

**Statement.** Let `R` be a unital ring, `N >= 3` and `ρ : St_N(R) -> Φ` a
homomorphism onto a finite group. Put `I = {r in R : ρ(x_12(r)) = 1}`. Then:
1. `I` is a two-sided ideal of finite index in `R`.
2. `ρ(x_ij(r)) = 1` for all `i != j` and `r in I`.
3. `ρ` factors through the natural surjection `St_N(R) -> St_N(R/I)`.

In particular, if `St_N(R)` is residually finite then so is `R`. If `0 != r` lies in
every finite-index two-sided ideal, then `x_12(r) != 1`, because it maps to
`e_12(r) != 1` in `E_N(R)`, but it dies in every finite quotient.
