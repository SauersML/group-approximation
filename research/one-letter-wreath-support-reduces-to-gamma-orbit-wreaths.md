---
rg: 2
id: one-letter-wreath-support-reduces-to-gamma-orbit-wreaths
kind: claim
title: Lamps with Gamma and one compressing letter generate a sofic group whenever every Gamma-orbit wreath is sofic
distinct_from:
  determinant-violation-needs-nonsofic-support-subgroup: that says a violation needs a nonsofic support subgroup; this computes when the support of one-letter lamp corners can be nonsofic at all
  compressing-letter-joins-whole-coset-blocks: that is the geometry of the coset percolation; this is the soficity bookkeeping of the same support
---

**ESTABLISHED.** Let `W = B x| G`, with `B = directSum_(G/Gamma) Z/2`, and
let `t` in `G` satisfy `t Gamma t^(-1) <= Gamma`. Put `G_t = <Gamma, t>`.

1. `B x| G_t` is sofic whenever `B x| Gamma` is sofic.
2. `B x| Gamma` is sofic iff every orbit wreath
   `(Z/2) wr_(Gamma/Gamma_x) Gamma` is sofic, where
   `Gamma_x = Gamma cap x Gamma x^(-1)`.

**Consequence.** An integral element over `W` supported on lamps,
`Gamma` and `t^(+-1)` violates the determinant conjecture only if some orbit
wreath of `Gamma` is nonsofic. That includes every lamp corner built from
`S` and `t`. The orbit of the coset `t Gamma` has stabilizer
`t Gamma t^(-1)`. Kun--Thom Theorem A certifies that orbit wreath nonsofic
when `t Gamma t^(-1)` is infranormal and not normal in `Gamma`, both being
Kazhdan. If no stabilizer is infranormal, one compressing letter is not enough,
and a witness needs letters generating a Kazhdan group containing `Gamma`
infranormally.
