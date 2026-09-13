---
rg: 2
id: finitary-centralizer-classifies-seam-normal-subgroups
kind: route
title: Centralizing every matrix transvection forces a scalar, then simplicity determines all normal subgroups
target: three-torsion-kazhdan-seam-is-just-non-mf
requires:
  - three-torsion-kazhdan-group-has-prescribed-simple-mf-factors
artifacts:
  - research/artifacts/pestov91-seam-normal-lattice-2026-09-13.md
  - research/artifacts/pestov91-heteroclinic-prescribed-mf-quotients-2026-09-13.md
---

The dense free seam orbit represents the ambient group faithfully on
the algebraic direct sum with basis `Z x {1,...,6}`. The kernel is the
full finitary linear group. Commuting with its transvections forces an
arbitrary linear automorphism to be scalar, hence identity over `F_2`.

For a normal subgroup `N`, simplicity of `L` makes `N intersection L`
either `1` or `L`. The first case forces `N` into the trivial
centralizer; the second says `L<=N`. Normal-subgroup correspondence
reduces all remaining cases to the product of two nonabelian simple
groups, whose only normal subgroups are products of factors. The
resulting four proper quotients are LEF, while the ambient MF radical
is nontrivial. Sections 1--3 give the entrywise centralizer proof,
the normal-lattice argument and all stated consequences.
