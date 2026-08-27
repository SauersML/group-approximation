---
rg: 2
id: nonhyperlinear-from-phase-safe-toric-gap
kind: route
title: Compile a phase-safe toric gap into a finitely presented nonhyperlinear group
target: non-hyperlinear-group
requires:
  - phase-safe-toric-gap-game-exists
  - phase-safe-toric-gap-implies-nonhyperlinear
artifacts:
  - notes/TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md
---

The nonlocal-game lane into the primary target, in the form the repository
has actually proved.  The second prerequisite is established: a finite
two-player toric game with finite phase group, `omega_qa < 1` and
`N ∩ B = {1}` yields the finitely presented nonhyperlinear group
`Q = Gtilde/N`.  The first prerequisite is the open half -- the game itself.

The route is worth stating separately from the other game-flavoured ideas in
this graph because of what it does *not* need.  There is no stability
hypothesis, no approximate-representation decoder, no rounding of quantum
objects to classical ones, and no appeal to soficity anywhere: a hypothetical
hyperlinear model is converted directly into a Connes-embeddable perfect
trace on a central phase corner.  What it does need is exactness -- perfect
completeness on the commuting side and an exact group relation -- which is
precisely the ingredient generic `MIP^*=RE` separations do not supply.

This route is now dead because its first prerequisite is refuted:
`normal-phase-safe-toric-games-have-qa-one` shows that normal phase safety
forces `omega_qa=1`.  The conditional implication remains valid but vacuous
for finite two-player torically determined games.
