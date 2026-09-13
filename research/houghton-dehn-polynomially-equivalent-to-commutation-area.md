---
rg: 2
id: houghton-dehn-polynomially-equivalent-to-commutation-area
kind: claim
title: "The Dehn function of H_n is polynomially equivalent to the area of commuting words with the basic transposition"
artifacts:
  - research/artifacts/zp-houghton-dehn-2026-09-13-part1.md
distinct_from:
  houghton-groups-have-polynomial-dehn-function: that asserts a polynomial bound, which is open; this is an established reduction that transfers any bound on one explicit relation family to the Dehn function, with a cubic loss.
  houghton-carmichael-sections-have-unbounded-edge-area: that shows areas of one family of Carmichael relators diverge; this bounds the whole Dehn function by commutation areas with the basic transposition, and conversely.
---

Let `n >= 3` and let `H_n` have Lee's presentation, with generators
`g_1, ..., g_(n-1), α`, where `α = ((1,1),(1,2))` (Lee, arXiv:1212.0257,
Theorem C). Define

```text
A(ℓ) = max { Area([z, α]) : z a word of length <= ℓ with zαz^(-1) = α in H_n }.
```

Then there is `C` with `A(L) <= δ(2L+2)` and `δ(L) <= C L^3 (A(CL) + 1)` for all
`L`. In particular `δ_(H_n)` is polynomially bounded if and only if `A` is, and
`A(ℓ) ≼ ℓ^k` gives `δ_(H_n)(x) ≼ x^(k+3)`.
