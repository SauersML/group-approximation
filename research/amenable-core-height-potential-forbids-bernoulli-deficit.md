---
rg: 2
id: amenable-core-height-potential-forbids-bernoulli-deficit
kind: claim
title: A Bernoulli witness pattern with a nonnegative height grading whose zero letters generate an amenable group has full value on every group
distinct_from:
  finite-core-height-potential-forbids-bernoulli-deficit: that assumes the zero-height core is finite, so regions invariant under the core exist; this allows an infinite amenable core, which needs anchored Følner frames in place of invariant regions.
  sofic-radical-localizes-bernoulli-deficit-witnesses: that needs soficity of the subgroup a witness generates; this would need only amenability of the zero-height core of one grading.
artifacts:
  - research/artifacts/height-graded-germ-models-2026-09-17.md
---

**OPEN.** Let `(k, E, F, psi)` be a configuration over a countable group `G`, with value `Phi`.
Suppose it admits a height potential `(a, b)`, as in
`finite-core-height-potential-forbids-bernoulli-deficit`, whose core `K_Z` is amenable. Then
`Phi >= log q`.

If this holds, every deficit witness over any group has a nonamenable core for every height
potential. That applies in torsion-free groups too, where the finite-core version never applies.

## Attempts

- **Anchored Følner frames (a-gs-kazhdan-rokhlin, 2026-09-17).** Section 4 of the artifact.
  - *Construction.* Replace the core-invariant regions by frames: a tile shape, a position inside
    it, and a coloring of a fixed region around the tile anchor.
    - The tiles come from a finite-radius rule that tiles each core coset by Følner tiles as a factor
      of the iid coloring.
    - A tile is accepted only if all its points compute it, and otherwise is a singleton.
    - Zero letters move within the tile, and positive letters drop a level and re-anchor.
  - *Counting.* Mass transport identifies the uniform count with the Palm measure of the tiling. The
    bad fraction is the boundary density plus the rule error plus the separation collisions.
  - **Missing:**
    - (1) A verbatim import of a finitary Følner tiling or quasi-tiling theorem for free p.m.p. actions
      of amenable groups: Ornstein--Weiss, or Conley--Jackson--Kerr--Marks--Seward--Tucker-Drob,
      Math. Ann. 2018. The graph has no such citation node.
    - (2) A written check that the tile of a translated position can be computed inside the shrunken
      region after every positive move, uniformly in the level.
  - **Scope of the method.** It cannot go further. For a nonamenable core, return pairs force the
    regions to form a cocycle along core moves, and that cocycle yields a Reiter measure on the core.
    The step is Section 5 of the artifact.
