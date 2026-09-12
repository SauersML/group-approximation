---
rg: 2
id: near-identity-embedding-forces-residual-nilpotence
kind: claim
title: Faithful near-identity representations force residual nilpotence
invalidates: [kl-via-magnus-near-identity-fixed-point]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Let `R` be a ring with a filtration by two-sided ideals
`R >= I >= I^2 >= ...` satisfying `I^r · I^s <= I^{r+s}` and
`∩_n I^n = 0`, and suppose a group `G` embeds in `(1 + I) ∩ R^x`.  Then

    [1 + I^r, 1 + I^s]  <=  1 + I^{r+s} ,

so `gamma_n(G) <= 1 + I^n` for every `n`, and separatedness gives
`∩_n gamma_n(G) = 1`: `G` is residually nilpotent.

A nontrivial **perfect** group has `gamma_n(G) = G` for all `n`, so it admits
no such faithful representation.

## What it kills, and why that is the whole class

The most natural universal construction for a one-variable equation is a
formal fixed point: put the coefficients near `1` in a complete filtered ring
— a Magnus embedding, a power-series or pro-nilpotent completion, a
near-identity operator algebra — and solve `w(t) = 1` by successive
approximation, the contraction being supplied by the filtration.  The method
is real and proves genuine special cases; it cannot be universal, because
`kl-counterexample-can-be-two-generator-simple` sends every hypothetical
counterexample into a simple, hence perfect, coefficient group, and this claim
says perfect groups are invisible to the method.

## Scope

The statement is about the *coefficient* group's representation.  It says
nothing against filtered or near-identity techniques used elsewhere in the
argument — for instance on the free factor, or after the coefficients have
already been placed by other means.  It also says nothing about groups that
are residually nilpotent, where such constructions remain available and
informative.
