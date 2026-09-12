---
rg: 2
id: symplectic-llp-positive-case-is-sp4
kind: claim
title: Any positive symplectic-lattice LLP case occurs at Sp4
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that asks whether any symplectic lattice has LLP; this proves that its only possible witness is the rank-two lattice Sp4(Z).
  sp4-llp-failure-or-maslov-nonhyperlinear-extension: that gives the Maslov dichotomy once the rank-two lattice is selected; this performs the rank reduction selecting it.
---

**ESTABLISHED.** If `C^*(Sp_(2g)(Z))` has LLP for some `g>=2`, then
`C^*(Sp_4(Z))` has LLP.

For `g=2` this is tautological. For `g>=3`, the Siegel Levi subgroup of
`Sp_(2g)(Z)` contains `SL_g(Z)`. Ioana--Spaas--Wiersma prove that
`C^*(SL_g(Z))` fails LLP for every `g>=3`, while LLP of full group
C-star algebras passes to subgroups. Hence no `g>=3` can be a positive
symplectic LLP case, leaving only `g=2`.

