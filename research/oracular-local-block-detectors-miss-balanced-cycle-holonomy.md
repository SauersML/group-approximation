---
rg: 2
id: oracular-local-block-detectors-miss-balanced-cycle-holonomy
kind: claim
title: Local matrix-block detectors for an oracular 2-CSP miss its balanced cycle holonomy
distinct_from:
  multiplicity-pi-turing-tape: that uses an authenticated isotypic multiplicity space as a dimension-reporting computation tape; this concerns local context packets whose multiplicities have already been balanced and proves they cannot read global marginal coherence.
  lin-gap-wrappers-retain-oracular-atlas-holonomy: that audits Lin's synchronous compression wrappers; this applies directly to the finite Culf--Mastel 2-CSP assignment diagram and isolates why canonical local type authentication is insufficient.
  amplification-natural-words-cannot-read-packet-multiplicity: that rules out reading anonymous spectator multiplicity; this allows exact reading of every local Plancherel multiplicity and shows that even those values contain no global cycle data.
---

Let `B` be a finite oracular 2-CSP.  For every queried edge `e=(x,y)`, a
perfect strategy gives an allowed-pair PVM

```text
{p_(e,a,b):(a,b) in R_e}
```

whose row and column sums are the marginal PVMs for `x` and `y`.  Pad and
split the atoms so that all local allowed-pair blocks have one common finite
signed-packet type.  In a canonical-profile matrix microstate, restriction
to that packet fixes the regular/Plancherel multiplicities, so an isotypic
block detector can authenticate every local block and every marginal rank.

Those data do not determine compatibility around a cycle.  Between two
incidences of the same marginal there remains a unitary on each equal-rank
multiplicity space.  Along a spanning tree these gauges can be chosen
independently.  On a chord their ordered product is an arbitrary cycle
holonomy.  Changing that product leaves every local packet representation,
its character, its block dimensions, and its marginal ranks unchanged.

Equivalently, the finite-sheet transport realization gives an exact
finite-dimensional model for every choice of those local ranks and every
finite monodromy permutation.  If local block data alone forced the marginal
equalities, applying the assertion to a Culf--Mastel NONHALT instance would
produce a perfect finite-dimensional 2-CSP strategy, contrary to its gap.

Thus a same-carrier challenge can use local block authentication as its
addressing layer, but the killing readout itself must depend on a
nontransport relative-position observable around a cycle.  Dimension
overflow or a multiplicity tape attached separately to each context is
blind to exactly the information that carries Culf--Mastel soundness.
