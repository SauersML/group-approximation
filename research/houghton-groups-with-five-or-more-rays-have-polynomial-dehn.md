---
rg: 2
id: houghton-groups-with-five-or-more-rays-have-polynomial-dehn
kind: claim
title: "For every n >= 5, Houghton's group H_n has Dehn function ≼ x^(6 + log_2 5)"
artifacts:
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
distinct_from:
  houghton-groups-with-six-or-more-rays-have-polynomial-dehn: that covers n >= 6 with exponent 8 and a log factor, using two auxiliary rays; this adds n = 5, using one auxiliary ray, with the weaker exponent 6 + log_2 5 < 8.33.
  houghton-groups-have-polynomial-dehn-function: that asserts a polynomial bound for every n >= 3; this proves it for n >= 5, and n in {3,4} stays open.
---

For every `n >= 5`, the Dehn function of Houghton's group `H_n` satisfies
`δ_(H_n)(x) ≼ x^(6 + log_2 5)`, for any finite presentation. In particular the
Dehn function of `H_5` is polynomially bounded.

Consequently, for `n = 5`, the commutation area of
`houghton-dehn-polynomially-equivalent-to-commutation-area` satisfies
`A(ℓ) <= δ(2ℓ+2) ≼ ℓ^(6 + log_2 5)`.

This answers the first question of Zaremsky Problem 1.24 ("Is it polynomial?") for
`n = 5`, beyond the known `n >= 6`. It says nothing about quadraticity, and nothing
about `n = 3, 4`.
