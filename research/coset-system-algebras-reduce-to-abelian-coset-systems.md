---
rg: 2
id: coset-system-algebras-reduce-to-abelian-coset-systems
kind: claim
title: Is the algebra of every coset system over finite groups the algebra of a coset system over abelian groups? Relabeling a given presentation can fail, so a proof must change presentation
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-relabeling-conjecture-2026-09-13.md
  - research/artifacts/ex-kac-quantum-compiler-q8-relabeling-counterexample-2026-09-13.md
  - research/artifacts/ex-kac-quantum-compiler-relabeling-collapse-2026-09-13.md
distinct_from:
  relabelable-coset-systems-are-solution-group-corners: that proves collapse onto a solution group for presentations that admit an affine relabeling; this asks whether every coset-system algebra has some abelian presentation, which would make every coset-system gap goal-level.
  exact-label-coset-refinements-are-affine: that treats coset refinements of Boolean context games whose blocks are exactly the shared-variable fibres; this concerns arbitrary coset systems over arbitrary finite groups, with no Boolean source and no label exactness.
  tracial-non-ru-coset-system-with-nonabelian-fibre-exists: that asks for a gap with a nonabelian fibre image; this asks whether every such algebra is already an abelian coset-system algebra.
---

**OPEN.**  Let `S` be a coset system (as in
`coset-systems-are-torsor-isomorphism-games`).  Decide whether there is always
a coset system `S^ab` over finite abelian groups with `A(S) ≅ A(S^ab)`.

**If yes.**  By `relabelable-coset-systems-are-solution-group-corners`
every coset-system gap is a finitely presented nonhyperlinear group, and coset
syntax never goes beyond `non-hyperlinear-group`.

**If no.**  A counterexample is the first syntax whose algebra sees
nonabelian local structure.  Even then it need not go beyond groups, since a
different presentation could still be a group-algebra corner.

**Correction (2026-09-13).**  The first version of this node conjectured that
every coset system admits an affine relabeling after support fixpoint and
holonomy pruning.  That form is false.  The Q_8 star below has no affine
relabeling, although its algebra is abelian.

## Attempts

- **Relabeling the given presentation.**  Sufficient for collapse
  (`relabelable-coset-systems-are-solution-group-corners`).  Where it dies:
  - Take the star of `Q_8` with three fibre products
    `K^(i) = {(g,h) : g C_i = h C_i}`, one for each cyclic `C_i ≅ Z_4`.
  - Each `K^(i)` carries the diamond `C_i x 1`, `1 x C_i`, `diag C_i`, with
    quotient leaves.
  - Albert's theorem forces the relabeling to be cyclic on each `C_i`-section
    of `Q_8`.  No abelian group of order 8 has three cyclic subgroups of
    order 4.
  - The algebra is nevertheless `C^8 (x) (C^4 * C^4 * C^4)`, an abelian
    coset-system algebra, because the leaves are redundant coarse-grainings.
  (Artifact part 6.)
- **Proved reductions that change nothing in the algebra (artifact part 5).**
  - Support fixpoint to a normal form: groups, normal-subgroup partitions,
    affine identifications.
  - Holonomy pruning: fixed sets of affine maps of groups are cosets.
  - A single Goursat relation is relabelable.
  - Two normal quotients glue as a fibre product.
  - A diamond of normal subgroups has abelian section.
- **Where the question now lives.**  In the Q_8 example the obstruction is a
  Latin-square isotopy class carried by redundant fibres.  An algebra-level
  obstruction needs the forcing fibres to carry independent PVMs glued to
  further structure.  No invariant of the algebra that detects the isotopy
  class is known here, and no example is known where it survives.
