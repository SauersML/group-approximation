---
rg: 2
id: rigid-hyperbolic-groups-contain-surface-subgroups
kind: claim
title: Every infinite hyperbolic group admitting no splitting over a finite or virtually cyclic subgroup contains a surface subgroup
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that is Gromov's question for all one-ended hyperbolic groups; this is its rigid case, which together with the surface-or-rigid dichotomy implies it
  kms-hb2-groups-contain-genus-two-surface-subgroups: that settles explicit hyperbolic Kazhdan KMS groups, which are rigid; this asks for every infinite rigid hyperbolic group
  wilton-no-2-torsion-surface-or-rigid-subgroup: that produces a surface subgroup or an infinite rigid subgroup; this asks for a surface subgroup inside the rigid groups themselves
---

**OPEN.** Let `R` be an infinite hyperbolic group which admits no nontrivial splitting, as an
amalgamated free product or HNN extension, over a finite or virtually cyclic subgroup. Then `R`
contains a subgroup isomorphic to the fundamental group of a closed surface with `chi < 0`.

This is Wilton's "rigid case" of Gromov's question. An infinite rigid group is one-ended by
Stallings, so the root claim implies this one. Conversely, this claim together with
`one-ended-hyperbolic-groups-contain-surface-or-rigid` implies the root, via
`one-ended-hyperbolic-surface-via-rigid-subgroups`.

## Attempts

- **Boundary dimension split.** The route `rigid-hyperbolic-surface-by-boundary-dimension`
  reduces the claim to two holes:
  - `menger-boundary-rigid-hyperbolic-surface-subgroups`;
  - `high-dim-boundary-rigid-hyperbolic-surface-subgroups`.

  Kapovich--Kleiner Theorem 4 leaves three one-dimensional cases:
  - the **Sierpinski carpet** case, now established as
    `carpet-boundary-hyperbolic-groups-have-surface-subgroups`;
  - the **circle** case, which gives a finite-index surface subgroup via
    `finite-by-cocompact-fuchsian-groups-are-virtually-surface`;
  - the **Menger curve** case, which is untouched.
- **Descent through one-ended subgroups.** This dies at termination. Wilton, arXiv:2406.02121
  (listing read 2026-09-16; not imported), shows that a cubulated hyperbolic group which is
  neither free nor a surface group has a one-ended quasiconvex subgroup of infinite index.
  Iterating gives chains of one-ended quasiconvex subgroups. No invariant was found that forces a
  chain to stop at a surface group, and the theorem produces no surface subgroup.
- **Covered rigid classes in the graph.**
  - Closed hyperbolic 3-manifold groups, whose boundary is `S^2`.
  - Uniform lattices with the flip assumption.
  - The six Kac--Moody--Steinberg families in `kms-hb2-groups-contain-genus-two-surface-subgroups`
    and the other `kms-*` claims. They have property (T), hence are rigid, for large primes.
  - These are all dimension-`>= 2` or special constructions, and none suggests a general
    mechanism.
