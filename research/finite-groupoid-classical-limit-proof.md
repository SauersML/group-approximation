---
rg: 2
id: finite-groupoid-classical-limit-proof
kind: route
title: Compute the sheet limit and compress the connected groupoid matrix units
target: finite-groupoid-diagonals-have-only-classical-gluing
requires: []
---

A unital homomorphism `C^k -> C^m` is pullback along a map from the `m`
target atoms to the `k` source atoms.  Applying this contravariant
description to every context and shared binary marginal gives `(FGD2)`.
A point of `Omega` chooses one allowed answer in every context and gives the
same value to every occurrence of a variable, hence is a classical BCS
assignment.  The converse is immediate.  This proves `(FGD3)` and the
strict-diagram assertion.

Choose one arrow from `o` to each object of a connected groupoid.  These
arrows give matrix units and the standard isomorphism `(FGD4)`.  Distinct
object identities are the diagonal matrix units.  The `o,o` compression
kills all but `1_o`, proving `(FGD5)`; conjugating any `1_y` back along the
chosen arrow gives `1_o`.  Keeping `r` object identities gives the upper
`r by r` matrix corner and its single coordinate diagonal `C^r`.

Transport around a chord acts on the root sheets by its isotropy/monodromy
element.  Retaining that element proves only conjugacy of the two coarse
projections.  Setting the two projections literally equal makes their
values agree on every root sheet and returns `(FGD2)`.  Finally, a graph of
finite connected groupoids is Morita-equivalent to a graph of finite
isotropy groups, whose fundamental isotropy group is virtually free.  Its
group factor and every finite matrix amplification are Connes embeddable,
so a unital corner representation of the fixed no-CE-trace BCS is
impossible.  These facts prove the stated trichotomy.
