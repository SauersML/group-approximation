---
rg: 2
id: pinch-and-round-retained-iwahori-residuals
kind: route
title: Round both sides of a supplied cut and erase only its positive-central block
target: iwahori-support-erasure-has-linear-commutator-leakage
requires: []
artifacts:
  - research/artifacts/iwahori-support-erasure-and-linear-leakage-2026-09-08.md
---

For a unitary `U` with `U^m=I`, pinch by `P,Q` to obtain
`A=PUP+QUQ`. Its distance from `U` equals `||[U,P]||` in both
HS and operator norm. Blockwise polar completion gives a unitary
`W` commuting with `P`, with
`||W-U||_2<=sqrt(2)||[U,P]||_2` and
`||W-U||_op<=2||[U,P]||_op`. Rounding its eigenvalues to nearest
`m`-th roots changes either norm by at most
`(pi/2)||W-U||`. Thus the resulting exact finite-order unitary
`V` commutes with `P` and has movement at most four times the HS
commutator and six times the operator commutator.

For each modular vertex, do this only inside the positive central
sector, using orders two and three, and leave the negative sector
unchanged. The resulting tuple `V` is an exact vertex pair with
the same central involution and with `P` reducing every generator.
The construction can be chosen unchanged outside the original
generator's cyclic span of `P`, of dimension at most
`2rank(P)` or `3rank(P)`.

Replace `V` on `P` by the trivial representation and retain it on
`Q`, obtaining `U_hat`. This pays at most `2sqrt(alpha)` beyond
the rounding movement and has the displayed rank bound. Since
every word is identity on the replaced block,
`R_a(U_hat)=Q R_a(V)Q`. Fixed-word telescoping between `V` and
`U` proves both retained-residual estimates in `(SEL1)`, and
`(SEL2)` proves the half-contraction.

The finite-order rounding ingredient is already present, with
coarser constants and a corner normalization, in
`round-finite-subgroup-corners-and-apply-block-capture`. The full
artifact supplies a self-contained proof for the simultaneous
HS/operator estimates, exact retention of the negative sector,
and the support-erasure budget used here. No bounded-payload
capture hypothesis is imported.
