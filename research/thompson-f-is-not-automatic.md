---
rg: 2
id: thompson-f-is-not-automatic
kind: claim
title: Thompson's group F admits no automatic structure
distinct_from:
  thompson-f-is-not-amenable: that claims F has no Følner sets; this claims no finite generating set of F carries an automatic structure, and no known theorem links the two
  thompson-f-is-automatic: that is the affirmative answer to the same named problem, Zaremsky Problem 2.2
artifacts:
  - research/artifacts/zp-thompson-f-automatic-2026-09-13.md
---

**OPEN.** No finite generating set of Thompson's group `F` carries an automatic
structure in the sense of Epstein et al., *Word Processing in Groups* (1992).

Routes that would establish it, all with open prerequisites:

- `thompson-f-not-automatic-via-finite-cd`: torsion-free automatic groups have
  finite cohomological dimension, and `F` does not
  (`thompson-f-has-infinite-cohomological-dimension`);
- `thompson-f-not-automatic-via-amenable-rigidity`: `F` is amenable, and amenable
  automatic groups are virtually abelian;
- `thompson-f-not-automatic-if-amenable-via-rips` (lane z4-01): `F` is amenable,
  and amenable automatic groups have contractible Rips complexes, which `F` lacks
  (`thompson-f-has-no-contractible-rips-complex`).

`automatic-groups-have-contractible-rips-complexes` feeds the first and third
routes.

## Attempts

- **Classical consequences of automaticity.** Dead as obstructions. Automatic
  groups are finitely presented, satisfy a quadratic isoperimetric inequality and
  are of type `F_∞`. `F` has all three (Guba, arXiv:math/0211395; Brown–Geoghegan
  1984).
- **Near-geodesic languages.** `thompson-f-has-no-near-geodesic-automatic-structure`
  (Hauze, Theorem 1.1) excludes languages over `{x0^±1, x1^±1}` with bounded
  additive excess over geodesic length. Automatic structures with uniqueness are
  multiplicative quasigeodesics (pumping argument in
  `zaremsky-2-02-thompson-f-automatic`), so extending Hauze to bounded
  multiplicative excess over every generating set is equivalent to this claim.
  That is a restatement, not a reduction, and no route is written for it.
- **Infinite dimensionality.** `F` is torsion-free of infinite cohomological
  dimension, so no Rips complex of `F` is contractible (both established). The
  general theorems that would turn this into non-automaticity are the open
  prerequisites of the routes above. No torsion-free automatic group of infinite
  cohomological dimension is known to this lane. By Kropholler's theorem
  (torsion-free LH𝔉 groups of type `FP_∞` have finite cohomological dimension),
  any such group lies outside LH𝔉, as `F` does.
