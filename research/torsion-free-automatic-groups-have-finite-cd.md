---
rg: 2
id: torsion-free-automatic-groups-have-finite-cd
kind: claim
title: Every torsion-free automatic group has finite cohomological dimension
distinct_from:
  thompson-f-has-infinite-cohomological-dimension: that is the established fact that F is torsion-free of infinite cohomological dimension; this is an open universal statement about automatic groups, which together with it would show F is not automatic
---

**OPEN.** If `G` is automatic (Epstein et al., *Word Processing in Groups*,
1992) and torsion-free, then `cd G < ∞`.

It matters here because `thompson-f-has-infinite-cohomological-dimension` and
this claim together give `thompson-f-is-not-automatic` (route
`thompson-f-not-automatic-via-finite-cd`).

## Attempts

- **Contractible Rips complexes.** For a torsion-free group, a contractible Rips
  complex gives finite cohomological dimension
  (`torsion-free-contractible-rips-complex-gives-type-f`). So
  `automatic-groups-have-contractible-rips-complexes` implies this claim (route
  `torsion-free-automatic-finite-cd-via-rips`). The obvious attempt at that
  prerequisite stops short. The synchronous fellow traveller property with
  constant `K` moves every vertex of a finite subcomplex of `P_d` one step back
  along its combing path while keeping `d`-close vertices `Kd`-close. That
  contracts `P_d` inside `P_(Kd)` (coarse contractibility, which gives type
  `F_∞`), not inside `P_d` itself. Dies at the change of scale.
- **Kropholler's theorem.** Torsion-free LH𝔉 groups of type `FP_∞` have finite
  cohomological dimension (Kropholler 1993; statement not re-read this session).
  Automatic groups are of type `F_∞`, so this claim holds for every automatic
  group in LH𝔉. A counterexample must lie outside LH𝔉, as `F` does.
- **Known automatic groups.** Every class checked has finite virtual cohomological
  dimension: hyperbolic groups, cocompactly cubulated groups, Garside and
  spherical Artin groups, mapping class groups, and closure under finite
  extensions, direct and free products. The check was bounded: standard classes
  only, no literature search.
- **Link to Problem 2.8.** If `every-torsion-free-f-infinity-group-of-infinite-cd-contains-f`
  holds (open, lane z2-08), a counterexample to this claim would contain a copy
  of `F`, so `F` is the canonical test object from both sides.
