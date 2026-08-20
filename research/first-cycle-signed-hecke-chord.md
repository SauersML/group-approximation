---
rg: 2
id: first-cycle-signed-hecke-chord
kind: claim
title: Close the first non-tree BCS overlap without changing the join-tree context partitions
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  simultaneous-block-escaping-context-holonomy: that asks for the complete coupled construction on every cycle; this assumes the exact join-tree atlas and isolates one additional chord.
  signed-hecke-block-escaping-cycle-holonomy: that is the full balanced atlas target; this is its first irreducible cyclic step.
---

Start with the explicit atlas of
`join-tree-bcs-has-explicit-signed-hecke-atlas`.  Let one additional incidence
identify variable `x` between two contexts whose current signed marginals are
`X_x^(0)` and `X_x^(1)` with equal canonical trace and equal finite packet
ranks.  Enlarge the finitely presented group and alter the context corner
unitaries, without changing their already valid context partitions, so that

```text
X_x^(0)=X_x^(1)                                           (FCH1)
```

holds as an exact algebraic identity.  All previous overlap identities and at
least one non-root assignment projection must survive.

## Attempts

- **A stable letter gives only conjugacy.**  Equal ranks provide an algebraic
  corner unitary carrying one sign to the other, but adjoining it records
  `UX_x^(0)U^*=X_x^(1)`, not `(FCH1)`.
- **Regauge one endpoint: breaks its tree separator.**  Conjugating the whole
  endpoint context to close the chord generally moves the marginals used to
  attach it to its parent.
- **Centralize the tree separator: exact criterion known.**  The allowed
  endpoint regauges are the commutants of their separator tuples.
  `sequential-marginal-holonomy-is-conditional-rank-matching` decides whether
  one endpoint can install the chord sign while fixing its separator, and
  `free-phase-context-escape-criterion` describes which separator blocks can
  additionally move genuine assignment atoms.
  `chord-regauging-is-relative-commutant-feasibility` now proves that the two
  endpoint orbits meet exactly when their transported separator algebras have
  a common-commutant involution realizing both conditional rank tables.  In
  particular they cannot meet inside any finite root block where the two
  separators generate the full matrix algebra.  The open construction is to
  manufacture that involution with finite group-word support in the escaped
  corner.
- **Finite target.**  Compute the double-orbit condition for the rational
  context partitions and realize a successful pair of endpoint regauges by
  free-phase corner unitaries.  Failure of every such double orbit would be a
  precise obstruction requiring a genuinely two-dimensional holonomy cell.
