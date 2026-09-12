---
rg: 2
id: prefix-corners-prove-full-leavitt-character-simplex
kind: route
title: Extend core character rigidity using split row shears and localized conjugacy orbits
target: binary-leavitt-full-character-simplex
requires:
  - degree-zero-leavitt-core-characters-are-dirac-haar-mixtures
  - binary-leavitt-elementary-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/leavitt-full-character-classification-2026-09-08.md
---

Use the uniform depth-two prefix identification `H=EL_4(R)` so that
the degree-zero core remains literally `K=(R_0)^x=EL_4(R_0)`.
The core-character prerequisite supplies its trivial weight `a`.
For each elementary generator, an infinite same-row root subgroup of
`K` commutes with that generator. Its invariant projection and the
invariant projection of `K` both have trace `a`, so they are equal.
Thus the core invariant projection is central for `H`; simplicity
makes its representation trivial.

On the complementary trace, the character is regular on `K`. First
consider a unit supported in a proper diagonal prefix corner. Refining
its complement provides two spare matrix coordinates. Elementary row
shears produce arbitrarily many conjugates whose pairwise quotients
are nontrivial split transvections conjugate to a constant core root.
Their GNS vectors are orthogonal, forcing character zero.

For any fixed unit `g`, finite prefix expressions for `g` and `g^-1`
show that a sufficiently deep cylinder `e` and its conjugate are both
supported in one proper diagonal corner `p`. Some such `H_e` has an
infinite conjugacy orbit of `g`: otherwise trivial centers and an
order-three corner unit force `g=1`. Pairwise quotients of those
conjugates lie in `H_p`, where vanishing was already proved. A second
orthogonality argument gives character zero at every `g!=1`.

The artifact proves the needed single-sandwich division by elementary
prefix cancellation and the transvection conjugacy using two spare
coordinates; no freeness assumption on arbitrary projective modules
or external full-group character theorem is hidden in these steps.
