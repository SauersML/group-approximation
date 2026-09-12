---
rg: 2
id: faithful-ah-irs-character-proof
kind: route
title: Apply the Glasner-Hase faithful IRS and compute its fixed-point character kernel
target: faithful-irs-blocks-naive-ah-character-rigidity
requires: []
artifacts:
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

Glasner--Hase Theorem 3.4 supplies a weakly mixing, nontrivial, faithful IRS
`theta` for every acylindrically hyperbolic group.  Formula `(FIR1)` is the
standard fixed-point character of an IRS.

The IRS kernel consists of the elements contained in the random subgroup
almost surely.  Its triviality therefore says `chi_theta(g)<1` for every
`g!=e`, which makes the character faithful.  Since the group is countable,
if every nonidentity `g` had containment probability zero, the probability
that the random subgroup contains any nonidentity element would also be
zero.  Nontriviality consequently supplies `g!=e` with
`chi_theta(g)>0`, proving nonregularity.

No step proves that the GNS von Neumann algebra of this character is a
factor.  The proof therefore stops at the all-character obstruction and
does not claim to settle a faithful-extremal-character gate.

