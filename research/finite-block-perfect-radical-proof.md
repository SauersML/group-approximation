---
rg: 2
id: finite-block-perfect-radical-proof
kind: route
title: Collapse one finite block and retain the free-product kernel to preserve finite presentation
target: finite-block-perfect-lamps-have-exact-mf-radical
requires:
  - finite-dimensional-kazhdan-fixed-algebra-transport
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
  - non_mf_groups_exist.tex
---

The block above tGamma+ is finite and Gamma-invariant. Each of its
coordinate elements is fixed by tGamma t^-1, so fixed-algebra transport
identifies its Gamma-conjugates. Distinct coordinates commute, forcing an
abelian image of K; perfection kills that image. Transitivity kills the
entire lamp kernel B_K. The residually finite quotient V then proves both
radical equalities.

The explicit presentation (8) imposes only finitely many within-block
commutators. Its normal form is the free product of the finite block groups,
semidirect V. Finite level-orbit windows are finite free products of finite
groups extended by residually finite actor groups with finite permutation
action; they are residually finite. The kernel of the height map is therefore
locally residually finite. The retained manuscript results
`prop:locally-rf-by-z-trace` and `thm:factorization-nonmf-trace`, together
with the classical sofic extension theorem, give the trace and sofic
conclusions. These retained trace results are the reason the current
manuscript remains in this route's artifact list.

Sections 3--4 of `research/artifacts/finite-block-perfect-mf-radicals.md`
prove the finite-block statements and the centerless A_5 specialization;
those sections are no longer being attributed to the current manuscript.
The perfect-group argument uses no MF-amalgam permanence theorem.
