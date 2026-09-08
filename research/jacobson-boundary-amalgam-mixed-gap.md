---
rg: 2
id: jacobson-boundary-amalgam-mixed-gap
kind: claim
title: The TS word and first braid have a positive matrix gap over the exact Jacobson boundary amalgam
distinct_from:
  jacobson-two-braid-mixed-packet-gap: that positivity statement is refuted by the seven-ray quotient; this imposes the additional shifted and boundary packet relations and includes the independent TS word.
artifacts:
  - research/artifacts/jacobson-boundary-amalgam-gap-equivalence-2026-09-08.md
  - research/artifacts/jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md
---

Prove `gamma_Xi>0` for the infimum defined in
`jacobson-boundary-amalgam-gap-characterizes-mark-collapse`.

The quantifier ranges over every matrix dimension and every complex
unitary representation type of both finite factors, agreeing on their
specified common subgroup and retaining `w_Q=x_13,Q`. An obstruction
only for natural linear or permutation models does not establish this
claim.

## Attempts

- The weaker two-braid presentation has a marked amenable quotient.
  That quotient violates the TS and boundary cells imposed here, so it
  does not settle this stronger infimum.
- Coherent finite-group correction makes the boundary packet exact
  while preserving the original packet. With both remaining relators
  exact, their consequences reconstruct a new finite subgroup with
  nine additive root coordinates. This does not yet give a uniform
  lower bound for approximate mixed relators.
- The faithful regular trace of the literal group restricts consistently
  to all these finite subgroups. Bare trace and rank equations cannot
  exclude arbitrary representation types. Opposite-root coherence and
  the unrestricted matrix obstruction remain unresolved.
- `jacobson-single-rank-one-root-orbit-cannot-extend` excludes the
  smallest nontrivial root orbit even with arbitrary root-trivial
  summands. It gives a positive gap on dimensions at most 97 by
  compactness. Coherent correction of both root packets strengthens
  this to the explicit bound `1/(8192*2,228,976)` on that dimension
  range. It does not control the remaining unbounded dimensions.
- The next fiber size is excluded by
  `jacobson-double-rank-one-root-orbit-cannot-extend`, raising the
  exact dimension lower bound to 147 and extending the same numerical
  gap through dimension 146. Three-dimensional fibers and the other
  nonzero root-character orbits remain unresolved.
- `jacobson-165-seed-fails-full-root-intersection` excludes the
  specified 147-dimensional carrier with a
  `chi_6,Q tensor sigma_3,P` complement, even with additional
  head-trivial, root-trivial spectators. Three boundary profiles match
  its entire smaller overlap, but one stabilizer character disagrees
  on the full root intersection. This excludes that seed rather than
  every representation of dimension 165; the general lower bound
  remains 147 and the unrestricted gap is still open.
