---
rg: 2
id: periodic-finitary-rank-compression-counterexample-proof
kind: route
title: Periodize finite intervals while retaining a full simple compression defect
target: uniform-finitary-rank-compression-is-mf-compatible
requires:
  - binary-finitary-transvection-uniformly-controls-active-rank
artifacts:
  - research/artifacts/uniform-finitary-rank-compression-counterexample-2026-09-08.md
---

The artifact explicitly embeds every finite multiplication table of
`GL_fin(Z,F_2) semidirect shift` in
`GL_N(F_2) semidirect C_N` by taking a sufficiently long cyclic interval.
The finite regular representations then give an injective norm-corona map.

The half-line subgroup is strictly compressed by the shift. Two displayed
transvections give the compression-centralizer defect `a=I+E_(-1,1)`.
An elementary commutator isolates a nonzero transvection in every nontrivial
normal subgroup of `GL_fin(Z,F_2)`, proving its simplicity. Its normal closure
is exactly the compression defect, since the quotient by it is abelian.

Finally apply the required uniform finite-group active-rank estimate to the
standard finite interval groups, conjugating the named transvection to a
standard root. No general transport theorem or approximation-permanence
theorem is used.
