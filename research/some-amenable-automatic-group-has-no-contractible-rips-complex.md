---
rg: 2
id: some-amenable-automatic-group-has-no-contractible-rips-complex
kind: claim
title: Some amenable automatic group has no contractible Rips complex
distinct_from:
  amenable-automatic-groups-have-contractible-rips-complexes: that is the affirmative answer to Zaremsky Problem 4.1; this is its negation
---

**OPEN.** There is an amenable automatic group `G` such that for every finite
generating set `S` and every `r >= 0` the Rips complex `P_r(G,S)` is not
contractible. (Negative answer to Zaremsky Problem 4.1, existential reading;
see `zaremsky-4-01-amenable-automatic-contractible-rips`.)

## Attempts

- 2026-09-13 (lane z4-01-amen-auto-rips): **infinite-dimensional candidates.**
  A torsion-free amenable automatic group of infinite cohomological dimension
  would be an example, by `contractible-rips-complex-gives-finite-classifying-space`.
  `F` would be one if it were both amenable and automatic
  (`thompson-f-has-no-contractible-rips-complex`). No such group is known to
  this lane.
- 2026-09-13: **excluded candidates.** Virtually abelian groups have contractible
  Rips complexes (`virtually-abelian-groups-have-contractible-rips-complexes`), and
  so does every group acting geometrically on an asymptotically CAT(0) space
  (`asymptotically-cat0-groups-have-contractible-rips`). A counterexample must
  therefore be an amenable automatic group that is not virtually abelian. For CAT(0)
  spaces the second exclusion follows from the first by the Adams–Ballmann theorem:
  amenable groups acting geometrically on CAT(0) spaces are virtually abelian (from
  memory, not re-read).
