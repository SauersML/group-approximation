---
rg: 2
id: sl2-half-stability-excludes-hnn-hyperlinearity
kind: claim
title: SL2(Z[1/2]) cannot be both flexibly HS-stable and have a hyperlinear HNN extension centralizing SL2(Z)
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - research/artifacts/sl2-hnn-iwahori-dynamical-fork-2026-08-21.md
distinct_from:
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that is the general theorem; this is its contrapositive specialized to the Dogon--Vigdorovich lattice, recorded because it turns the open question into a dichotomy with a concrete second horn.
---

Let `G_2 = < SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1 > = SL_2(Z[1/2]) *_(SL_2(Z))
(SL_2(Z) x Z)`.  Then at least one of the following holds:

1. `G_2` is not hyperlinear (and is then an explicit finitely presented
   nonhyperlinear group);
2. `SL_2(Z[1/2])` is not flexibly Hilbert--Schmidt stable, i.e.
   `iwahori-local-global-defect-question` has a negative answer.

*Proof.*  `hnn-over-codense-kazhdan-subgroup-not-hyperlinear` with the pair
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`. ∎

**What the second horn would need.**  Microstates for `G_2` restrict to
microstates `U_n` of `SL_2(Z[1/2])` together with unitaries `U_n(t)`
almost commuting with `U_n(SL_2(Z))` but with `tr U_n([t, a]) -> 0` for
`a notin SL_2(Z)`.  By the theorem's proof, `U_n` cannot be near exact
(congruence) representations, since there the (tau) gap and co-density
force `U_n(t)` into the commutant of the whole base.  So hyperlinearity
of `G_2` is equivalent to the existence of *exotic* microstates of
`SL_2(Z[1/2])` -- far from all congruence representations -- that admit
such an almost-centralizer of `SL_2(Z)`.  Producing them would refute the
stability of `SL_2(Z[1/2])` (and hence close the Dogon--Vigdorovich route
negatively); failing to produce them is no evidence either way.

**Amalgam form.**  `G_2` is an amalgamated free product of two residually
finite hyperlinear groups over the virtually free group `SL_2(Z)`.
Hyperlinearity is known to pass through amalgams over amenable subgroups
(`amenable-edge-hnn-preserves-hyperlinearity`); a permanence theorem for
amalgams over virtually free subgroups would therefore settle the
dichotomy in favour of horn 2.
