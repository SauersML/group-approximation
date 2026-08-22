---
rg: 2
id: atlas-m24-marked-packet-collision-exclusion
kind: claim
title: The augmented Atlas packet has no generating marked A8 pair in M24
distinct_from:
  atlas-a4-m23-packet-double-coset-screen: that excludes only pairs inside M23; M24 also has M22:2 and affine carriers and cross-carrier pairs.
  atlas-m24-a8-three-carrier-fork: that reduces the carrier sources but does not classify their ambient fusion or screen marked pairs.
---

It remains to prove that no pair of marked `A8` subgroups in `M24` both
generates `M24` and satisfies the twelve Atlas packet edges together with
collision `19243` and `q14`.

The exact structural reduction `atlas-m24-a8-three-carrier-fork` leaves only
the `M23`, `M22:2`, and `2^4:A8` carrier sources.  Same-`M23` pairs are already
excluded by `atlas-a4-m23-packet-double-coset-screen`; ambient fusion and the
remaining same-/cross-carrier cells are open.

## Attempts

An exact GAP carrier-fusion audit using `MaximalSubgroupClassReps(M24)` was
stopped at its strict 300-second cap before returning a first record.  No
partial computational assertion is retained.  The next bounded attack must
construct the three carrier representatives directly (or use character-table
marks) and determine ambient fusion before enumerating any packet fiber.
