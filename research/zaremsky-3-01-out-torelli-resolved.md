---
rg: 2
id: zaremsky-3-01-out-torelli-resolved
kind: claim
title: "Decide whether the Torelli group of Out(F_n) is finitely presented for all large n"
---

Part of Zaremsky Problem 3.1 (`zaremsky-3-01-torelli-groups-finitely-presented`).
Let `T_n = ker(Out(F_n) -> GL_n(Z))`. This claim is the question for this family.
It is established by exactly one of two routes:

- **Yes**: `zaremsky-3-01-out-by-yes` requires `outer-torelli-groups-fp-for-large-rank`.
- **No**: `zaremsky-3-01-out-by-no` requires
  `outer-torelli-groups-not-fp-for-infinitely-many-ranks`.

As a bare disjunction this is a classical tautology. Its content is knowing which
disjunct holds, so no `requires: []` route may be written into this claim.
