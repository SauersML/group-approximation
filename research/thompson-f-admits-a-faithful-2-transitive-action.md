---
rg: 2
id: thompson-f-admits-a-faithful-2-transitive-action
kind: claim
title: Thompson's group F admits a faithful 2-transitive action
---

There is a set `Ω` with `|Ω| ≥ 3` and a faithful action of Thompson's group `F`
on `Ω` that is transitive on ordered pairs of distinct points. Equivalently,
there is a core-free subgroup `H < F` with exactly two `(H,H)`-double cosets,
`F = H ⊔ HgH`. Together with `thompson-f-transitivity-degree-at-most-two`,
this would give `td(F) = 2`.

## Attempts

- 2026-09-13 (z2-20-f-2-transitive): candidates for `H` are maximal subgroups of
  infinite index. The stabilizers of points of `(0,1)` fail, since those actions
  preserve the order. Le Boudec–Matte Bon (arXiv:1906.05744, p. 23) suggest the
  stabilizers of partitions of an `F`-orbit in `[0,1]`, such as the maximal
  subgroups of Golan–Sapir (J. Algebra 470 (2017) and Trans. AMS 369 (2017)).
  Any candidate must pass these tests:
  - the grid condition of Proposition 5.1(2): for each `x ∈ (0,1)`, orbits of
    `F_x^-` and `F_x^+` on `F/H` meet in at most one point;
  - no binary `F`-invariant relation on `F/H` other than equality and its
    complement, for example relations built from order or germs of associated
    closed sets.
  Not yet tested on a concrete candidate.
