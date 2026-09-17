---
rg: 2
id: houghton-groups-with-six-or-more-rays-have-polynomial-dehn
kind: claim
title: "For every n >= 6, Houghton's group H_n has Dehn function ≼ x^8 log x"
artifacts:
  - research/artifacts/zp-houghton-pours-2026-09-17.md
distinct_from:
  houghton-groups-have-polynomial-dehn-function: that asserts a polynomial bound for every n >= 3; this proves it only for n >= 6, and n in {3,4,5} stays open.
  houghton-transposition-commutation-area-is-polynomial: that is a polynomial bound on commutation areas with α for every n >= 3; this is the Dehn function for n >= 6, and it gives that bound for n >= 6 through A(ℓ) <= δ(2ℓ+2).
  houghton-dehn-polynomially-equivalent-to-commutation-area: that is a reduction with no bound on A; this proves a bound without bounding A first, through path words built from halving pours.
---

For every `n >= 6`, the Dehn function of Houghton's group `H_n` satisfies
`δ_(H_n)(x) ≼ x^8 log x`, for any finite presentation. In particular it is
polynomially bounded.

Consequently, for `n >= 6`, the commutation area of
`houghton-dehn-polynomially-equivalent-to-commutation-area` satisfies
`A(ℓ) <= δ(2ℓ+2) ≼ ℓ^8 log ℓ`.

This answers the first question of Zaremsky Problem 1.24 ("Is it polynomial?") for
`n >= 6`. It says nothing about quadraticity, and nothing about `n = 3, 4, 5`.
