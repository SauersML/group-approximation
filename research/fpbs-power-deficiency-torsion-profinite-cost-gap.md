---
rg: 2
id: fpbs-power-deficiency-torsion-profinite-cost-gap
kind: claim
title: A residually-p torsion group of positive power p-deficiency has every profinite boundary action of cost at least 1+delta, so it is not of fixed price one
distinct_from:
  fpbs-power-p-deficiency-schreier-bound: that is the Schlage-Puchta subnormal p-gradient inequality; this passes it to all finite-index subgroups of the residual p-torsion image, uses rank instead of mod-p rank, and converts it into a lower bound for the cost of every Farber boundary action.
  fpbs-kazhdan-positive-rank-gradient: that asks for positive gradient in a Kazhdan group, where Hutchcroft-Pete supply the cheap action; this group has positive gradient unconditionally but no property (T), so its cheap side is missing.
  fpbs-burnside-positive-upper-cost: that is a lower bound for Bernoulli cost of bounded-exponent Burnside groups, which have no Farber chains; this is a lower bound for profinite actions of a residually finite torsion group of unbounded exponent.
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

Fix a prime `p`. Enumerate `F(x,y) = {w_1, w_2, ...}` and put
`Gamma = <x,y | w_i^(p^(i+1)), i >= 1>`. Let `Gamma'` be its image in its
pro-`p` completion, and put `delta = 1 - 1/(p(p-1))`.

Then `Gamma'` is an infinite 2-generated residually finite `p`-torsion group
of unbounded exponent, and it has no property (T). Every finite-index
subgroup `U' <= Gamma'` satisfies `(d(U')-1)/[Gamma':U'] >= delta`.

Consequently every Farber chain of `Gamma'` has gradient at least `delta`, and
its boundary action is a free p.m.p. action of cost at least `1 + delta`. So
`Gamma'` does not have fixed price one. It refutes fixed price as soon as some
free action of `Gamma'` costs less than `1 + RG(Gamma')`, where `RG` is the
infimal rank gradient.
