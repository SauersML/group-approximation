---
rg: 2
id: zaremsky-3-01-by-all-three-families
kind: route
title: "Zaremsky 3.1 is resolved once each of the three Torelli families is decided"
target: zaremsky-3-01-torelli-groups-finitely-presented
requires:
  - zaremsky-3-01-out-torelli-resolved
  - zaremsky-3-01-surface-torelli-resolved
  - zaremsky-3-01-aut-torelli-resolved
---

Problem 3.1 asks about three families at once: the Torelli groups of `Out(F_n)`,
of `MCG(S_g)` and of `Aut(F_n)`. It is answered when each family's eventual
finite presentability is decided, in either direction. This is the only admissible
route into the root.

The Aut and Out resolutions are logically tied: `ia-n-fp-iff-outer-torelli-fp`
transfers each answer between them. The surface family is independent of both.
