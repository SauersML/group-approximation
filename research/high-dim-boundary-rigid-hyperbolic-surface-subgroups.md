---
rg: 2
id: high-dim-boundary-rigid-hyperbolic-surface-subgroups
kind: claim
title: Every rigid hyperbolic group whose boundary has dimension at least two contains a surface subgroup
distinct_from:
  closed-hyperbolic-3-manifold-groups-contain-surface-subgroups: that is the Kahn--Markovic case of closed hyperbolic 3-manifold groups, whose boundary is S^2; this asks for every rigid hyperbolic group with boundary of dimension at least two
  flip-uniform-lattices-contain-surface-subgroups: that covers uniform lattices satisfying the flip assumption; this asks for arbitrary rigid hyperbolic groups of boundary dimension at least two
  rigid-hyperbolic-groups-contain-surface-subgroups: that is the whole rigid case; this is its part of boundary dimension at least two
---

**OPEN.** Let `R` be a hyperbolic group which admits no nontrivial splitting over a finite or
virtually cyclic subgroup, and whose Gromov boundary has topological (covering) dimension at least
`2`. Then `R` contains a subgroup isomorphic to the fundamental group of a closed surface with
`chi < 0`.

## Attempts

- **Boundary `S^2`, via Cannon's conjecture (open).**
  - Cannon's conjecture would make `R` finite-by-cocompact-Kleinian. Selberg's lemma then gives
    a torsion-free finite-index Kleinian subgroup, that is, a closed hyperbolic 3-manifold group.
  - By `closed-hyperbolic-3-manifold-groups-contain-surface-subgroups` it contains a surface
    group `S`.
  - The preimage of `S` in `R` is finite-by-cocompact-Fuchsian, so
    `finite-by-cocompact-fuchsian-groups-are-virtually-surface` gives a surface subgroup of `R`.
  - This only trades the case for Cannon's conjecture.
- **Uniform lattices.**
  - Uniform lattices with the flip assumption are covered
    (`flip-uniform-lattices-contain-surface-subgroups`).
  - Cocompact lattices in `SO(2n,1)`, `n > 1`, are covered by Kahn--Rao, arXiv:2503.20759
    Theorem 1.1 (v4, 14 Nov 2025; read from the arXiv listing 2026-09-16, not imported).
  - These are special geometric classes, and the mechanism (good pants and mixing of the frame
    flow) needs a homogeneous structure that a general hyperbolic group lacks.
- **Peripheral structures.** Dimension `>= 2` gives no analogue of the one-dimensional peripheral
  circle mechanism. Kapovich--Kleiner's classification is specific to dimension `1`.
