---
rg: 2
id: non-group-dual-colored-qc-qa-pair-exists
kind: claim
title: Some pair of finite colored digraphs whose quantum symmetry is not a group dual is qc- but not qa-isomorphic
distinct_from:
  qc-isomorphic-not-qa-isomorphic-graph-pair-exists: that asks for any qc-but-not-qa pair of plain graphs, with no condition on the quantum symmetry; this asks for colored digraphs and requires the quantum symmetry of their union to be genuinely quantum, not dual to a group.
  non-ce-quantum-automorphism-group-of-finite-graph-exists: that asks for a finite plain graph with non-embeddable quantum automorphism group, which a solution-group gap already supplies; this asks for a colored pair whose non-embeddable symmetry is not a group dual.
  colored-cfi-rung-is-the-solution-group-case: that shows colored CFI pairs carry exactly solution-group duals; this asks for the part of the rung beyond group duals.
---

**OPEN.**  Find finite colored digraphs `X, Y` such that:

- `X ≅_qc Y`, but `X` and `Y` are not `qa`-isomorphic (definitions as in
  `closure-safe-support-is-exactly-the-colored-iso-rung`);
- `Qut(Z)`, for `Z = X ⊔ Y` with a new cross colour, is not dual to a discrete
  group, i.e. `O(Qut Z)` is not cocommutative.

**Consequence.**  By the last part of
`closure-safe-support-is-exactly-the-colored-iso-rung`, `Qut Z` is then a Kac
compact quantum group of a finite structure.  Its Haar von Neumann algebra is
not Connes embeddable, and it is not a group dual.  This would be a
non-embeddable quantum symmetry that is genuinely quantum.

**Relation to the goal.**

- A finitely presented nonhyperlinear group gives such a pair trivially.
  - Take the colored CFI pair of a tracial non-`R^U` linear system.
  - Adjoin to both graphs one unconstrained torsor fibre of `S_3`.
  - By `coset-systems-are-torsor-isomorphism-games` (T3, T4) the enlarged pair
    keeps the gap and has a symmetry that is not a group dual.
- The converse direction is the point.  Instances where nonabelian local
  symmetry carries the gap are not known to give a nonhyperlinear group.

**Syntax.**  `coset-systems-are-torsor-isomorphism-games` reduces the problem,
on torsor digraphs, to a tracial non-`R^U` coset constraint system with a
nonabelian fibre image: `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`.
Pairs whose fibres are not torsors are not covered by that reduction.
