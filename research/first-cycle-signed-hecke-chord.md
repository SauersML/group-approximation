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
- **Commuting-separator subcase: reduced to max flow.**
  `commuting-separator-chord-is-capacitated-transport` proves that if the two
  transported separator algebras commute, the common involution exists
  exactly when one finite integral transportation problem satisfies its cut
  inequalities.  Joint block dimensions are capacities and the two
  conditional rank tables are its demands.  A successful construction may
  therefore target commuting escaped separators with adequate joint block
  capacity; otherwise it must solve the genuinely noncommuting relative-
  commutant problem.
- **The general finite target is now algorithmic.**
  `finite-relative-commutant-chord-is-bounded-integer-feasibility` eliminates
  the unknown common involution and gives one bounded Wedderburn integer
  system, without assuming that the separators commute.  Equal total ranks
  alone fail already for the transverse Pauli separators in `M_2(C)`.
- **The acyclic ambient group cannot contain the finished answer.**
  `cycle-closure-cannot-remain-in-the-join-tree-group` proves that the direct
  product of the finite packet and the fresh free-phase groups is residually
  finite.  Completing every chord in that unchanged corner would create a CE
  trace on the no-CE BCS.
- **Finite-edge HNN transport is exact but globally dead.**
  `finite-character-idempotents-have-exact-hnn-transport` shows that matched
  finite-subgroup character pieces can be transported and assembled exactly.
  However `finite-edge-hnn-closures-cannot-finish-the-nonce-atlas` proves that
  finite iterations of these HNN extensions remain residually finite.  The
  decisive chord must use an infinite associated subgroup or another
  genuinely non-residual-finiteness-preserving extension.
- **A dense infinite-edge literalization collapses to a mapping torus.**
  `britton-support-traps-dense-free-phase-chord` proves the converse support
  rule for additive HNN transport: if `tXt^(-1)` returns to the base group
  algebra, every coefficient in `supp(X)` must lie in the associated
  subgroup.  A dense escaped free-phase marginal has support generating the
  whole effective packet group `K_D times L_D`.  Transporting two such
  marginals therefore forces a whole-base automorphism HNN, which is
  hyperlinear.  A live infinite-edge chord must be separator-block sparse,
  genuinely multi-piece/non-graphical, or non-HNN.
