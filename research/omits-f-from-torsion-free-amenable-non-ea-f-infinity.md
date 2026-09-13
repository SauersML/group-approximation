---
rg: 2
id: omits-f-from-torsion-free-amenable-non-ea-f-infinity
kind: route
title: A torsion-free amenable non-EA F_infinity group answers Zaremsky 2.8 if Kropholler's question holds and F is not amenable
target: some-torsion-free-f-infinity-group-of-infinite-cd-omits-f
requires:
  - there-is-torsion-free-f-infinity-amenable-non-ea-group
  - amenable-groups-of-finite-cd-are-virtually-solvable
  - thompson-f-is-not-amenable
---

Let `G` be torsion-free, amenable, not elementary amenable, and of type `F_∞`
(`there-is-torsion-free-f-infinity-amenable-non-ea-group`).

1. **`cd G = ∞`.** Otherwise `G` is amenable of finite cd, hence virtually
   solvable (`amenable-groups-of-finite-cd-are-virtually-solvable`). Virtually
   solvable groups are elementary amenable, which contradicts the choice of `G`.
2. **`G` contains no copy of `F`.** A subgroup of an amenable group is
   amenable, and `F` is not amenable (`thompson-f-is-not-amenable`).
3. So `G` is torsion-free, of type `F_∞`, has infinite cd, and omits `F`,
   which is the target (the affirmative answer to Zaremsky 2.8).

All three premises are open, so this route does not establish its target.
