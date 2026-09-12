---
rg: 2
id: kun-thom-wreath-galois-unequal-atomic-element
kind: claim
title: A Kun--Thom wreath has an integral self-adjoint element with purely atomic spectrum and Galois-unequal conjugate masses
distinct_from:
  determinant-conjecture-counterexample-exists: that asks for any violating group and matrix; this asks for one specific shape, a purely atomic Galois-unequal spectrum, over one specific nonsofic group
  determinant-violation-needs-nonsofic-support-subgroup: that is a necessary condition on supports; this is a concrete witness shape that would meet it
---

**OPEN.** For a Kun--Thom wreath `W = (Z/2) wr_(G/Gamma) G`
(`kun-thom-nonsofic-wreath`), find a self-adjoint `A in M_n(Z[W])` whose
spectral measure is purely atomic at algebraic integers, with two Galois
conjugates carrying different von Neumann multiplicity. By
`atomic-serre-measures-are-equal-weight-real-orbits` such an `A` violates the
determinant conjecture.

## Attempts

- **Kazhdan projection conjugation.** Dead: the projection is `0` in `L(W)`
  (`kazhdan-projections-vanish-in-regular-group-algebra`).
- **Supports inside the lamps or inside `G`.** No violation there: the
  lamps generate a locally finite subgroup and `G` is residually finite
  (`determinant-violation-needs-nonsofic-support-subgroup`). A witness must
  mix lamps with letters of `G` whose generated subgroup is nonsofic. Whether
  `B x| Gamma` is sofic is not settled here, because the stabilizers
  `Gamma cap x Gamma x^(-1)` of its orbits need not be separable.
- **Lamp-corner model.** With `P = 1 + e_Gamma`, the corner `P X P` for
  `X in Z[G]` is `X` restricted to a random union of right cosets of `Gamma`
  (`wreath-lamp-corner-is-coset-percolation`). `Gamma`-supported `X` gives only
  sofic atoms.
- **Finite coset clusters under one compressing letter.** Dead: blocks are
  infinite, so there are no finite clusters
  (`compressing-letter-joins-whole-coset-blocks`).
- **Support of one-letter corners.** Lamps, `Gamma` and one compressing `t`
  generate a sofic group unless some orbit wreath of `Gamma` is nonsofic
  (`one-letter-wreath-support-reduces-to-gamma-orbit-wreaths`). For a
  monomial-substitution letter, `t Gamma t^(-1)` is not infranormal in
  `Gamma` (`substituted-elementary-subgroup-is-not-infranormal`), so these
  supports carry no certified nonsofic wreath.
- **Certified support, open.** Lamps, `Gamma` and compressing letters that
  generate `SL_d(Z)`, such as the nonnegative elementary matrices, generate
  `B x| G`, which contains Kun--Thom's nonsofic wreath. The corner model still
  has infinite blocks, now joined by several letters whose block digraphs have
  out-degree one. The next computation is compactly supported eigenvectors of
  such a corner.
