---
rg: 2
id: openai-leavitt-unit-nonsofic-proof
kind: route
title: Apply the expander-matching criterion to the nine-leaf configuration, with Thompson's V as the witness
target: openai-leavitt-unit-nonsofic
requires: [openai-expander-matching-criterion, openai-nine-leaf-leavitt-configuration, thompson-v-not-lef]
artifacts:
  - c1168433:official/counterexample.tex
---

## Why sufficient

This is the chapter's own proof of Theorem 1.1, in three lines once the
prerequisites are in hand.

The second prerequisite says that `Gamma = EL_alpha(R)`, `G = EL_D(R)`,
`J = V_(1000)`, `t_1 = u`, `t_2 = v` satisfy every hypothesis of the first.
So if `G` were sofic, the first prerequisite would force `J` to be LEF.  The
third says `J =~ V` is not LEF.  Therefore `G` is not sofic.  `G <= R^x` and
soficity passes to subgroups, so `R^x` is not sofic either.

## Where the contradiction actually bites

Worth naming, because the shape is reusable: the criterion converts a global
approximation property of the big group into an *exact* finite-model property
of a small commuting subgroup.  Soficity is an approximate, error-tolerant
statement; LEF is exact.  The compressions are what remove the error, by
forcing all the relevant action onto one expanding component, and the witness
only has to be a group for which no exact finite model exists.  Any finitely
generated non-LEF group in the right position would do; `V` is chosen because
it is finitely presented, infinite and simple, and because the prefix
structure of the Leavitt algebra puts a copy of it exactly where the criterion
needs one.

## The two ranks

`G =~ EL_9(R)` and `Gamma =~ EL_3(R)`.  Nine leaves are what the two
compression tables need -- three blocks of three, so that `u` and `v` can each
map one block into `[alpha_i 1]` and the other onto `[zeta_i]`.  The rank is
not forced by the criterion, and this repository's own endpoint runs the same
mechanism at rank four; see
[[openai-leavitt-unit-nonsofic-from-formalized-endpoint]].
