---
rg: 2
id: globally-conditioned-v4-exit-capacity
kind: claim
title: Couple all V4 failure blocks through one shared non-CE contextual capacity ledger
distinct_from:
  same-context-s3-endpoint-atlas: that asks for an unconditional bounded cell around one context and is therefore already a root-level nonhyperlinearity criterion; this requires one joint construction whose capacity proof retains cross-context operator data.
  non-ce-bcs-has-robust-approximate-energy-gap: that gives a matrix-only gap for the original shared selector tuple; this must transport the corresponding operator-valued contextual defect through the V4 packet exits without reducing it to scalar forbidden mass first.
  multiplicity-return-transducer: that states the full fixed-packet return architecture; this pins its remaining finite-dimensional invariant to one global family of source and exit projections with a trace-capacity ledger.
---

For the fixed BCS `B` with a tracial state and no Connes-embeddable tracial
state, construct one finitely presented marked group `(Gamma,w)` containing
the context packet words and shared selector words, together with the
following decoder for every sufficiently accurate marked matrix microstate.

After fixed-group exactification, let `P_c` be the forbidden carrier of
context `c` and let `F_(c,b)`, `b in {00,01,11}`, be its three synchronized
V4 failure projections.  Produce transported exit projections `E_(c,b)` and
unitaries `U_(c,b)` such that

```text
sum_(c,b)||U_(c,b)F_(c,b)U_(c,b)^*-E_(c,b)||_2^2
  <= C E_rel+o(1),                                       (GVC1)

sum_(c,b)tau(E_(c,b))
  <= sum_c tau(P_c)+C E_rel+o(1).                        (GVC2)
```

The control term `E_rel` must be a bounded-overlap sum of defining-relator
energies **before local context copies are separated**, and the proof of
`(GVC2)` must use a cross-context operator observable built from the same
shared selector words.  It may be an intertwiner Gram matrix, a two-cell
holonomy operator, or an equivalent global moment matrix.  It may not factor
through the scalar list `(tau(P_c))_c`.

The completeness half only needs some exact unitary representation witnessing
`w!=1`; it need not extend the non-CE trace through the groupifier.  By
`kleene-completeness-needs-only-a-nontrivial-exact-representation`, this
witness may use properly infinite multiplicity to absorb the return cell.
On finite-dimensional microstates,
`non-ce-bcs-has-robust-approximate-energy-gap` either already makes `E_rel`
positive or leaves positive total forbidden carrier.  In the latter case,
sum the three identities `(VOF5)` and apply
`five-fourths-projection-surplus-pays-linear-hs-energy` to `(GVC1)--(GVC2)`:

```text
E_rel >= c sum_c tau(P_c)-o(1).                          (GVC3)
```

The robust BCS gap then gives a fixed total energy floor.

The global-use clause is mandatory.  If `(GVC1)--(GVC2)` decomposes into one
unconditional statement per context, then
`single-context-v4-exit-capacity-is-already-nonhyperlinearity` shows that the
first context cell alone is already the desired nonhyperlinear group, and the
claimed reduction has merely hidden the whole open problem in a local lemma.

## Attempts

- **Scalar forbidden-mass routing is rejected.**  It forgets why the BCS has
  no CE trace and triggers the single-context circularity theorem.  No list of
  contextwise restriction multiplicities is accepted as the global datum.
- **Use the exit cross-Gram matrix.**
  `global-v4-exit-capacity-is-cross-gram-curvature` reduces the analytic
  target to partial isometries with the prescribed failure sources and the
  bound `(VGC5)`.  Their cross-Gram entries are range overlaps, and when the
  ranges are context atoms they are cross-context trace words in the original
  shared selectors.  This is the active attack because it retains precisely
  the operator data absent from scalar type flow.
- **The analytic capacity now has a finite tag certificate.**
  `disjoint-tag-covariance-controls-cross-gram` proves that if the exit maps
  carry pairwise disjoint types of one fixed finite tag group and those types
  are absent outside the parent, then both off-parent leakage `l` and the full
  ordered cross-Gram overlap `o` are bounded by covariance-relator energy,
  with a constant independent of all multiplicities and of matrix dimension.
  `shared-context-exclusive-v4-tagging` is now the sole construction gate:
  extract those exclusive tags jointly from the original shared-context tuple
  while preserving the allowed exact tracial extension.
  Adjoining unrelated tags separately to each local packet is not accepted:
  that would bypass, rather than use, the contextual compatibility data.
- **Projection recurrence splice.**  On the Fanizza doubling source,
  `fanizza-doubling-carriers-form-orthogonal-flag` converts the exact carrier
  propagation to a commuting involution word and identifies its entire
  nonlinear residual as `2AB`, with squared HS mass `4tau(AB)`.  Thus a
  cross-Gram decoder need not transport an anonymous additive recurrence: it
  may target these overlap projections directly.  The global-use condition
  remains mandatory, since an unconditional one-overlap discharge would
  already be a root-level nonhyperlinearity criterion.
- **Independent local exactification is insufficient.**  Choosing a separate
  Gowers--Hatami correction for every packet gives unrelated conjugating
  isometries and leaves the cross-Gram matrix unconstrained.  The branch maps
  must be extracted from the original shared-word tuple first, or from one
  simultaneous correction on an overlap complex.
- **Properly infinite completeness is allowed.**  The exit atlas may close in
  one exact infinite-multiplicity representation even when its finite rank
  ledger is overdetermined.  The capacity estimate must nevertheless remain
  matrix-only; asserting it for every tracial representation would trigger
  the regular-trace obstruction.
- **Sparse support-packet coefficient enrichment stops at two tags.**
  `support-packet-five-sparse-wedderburn-tag-capacity-is-two` exhausts all
  coefficients through five irreducible summands.  Every pointwise
  allowed-flat class has at most two forbidden commutant types, not the five
  required exit labels.  This does not rule out automorphism-permuted allowed
  profiles, larger coefficients, or contextual cross-copy decoders.
- **Deferred finite computation.**  For a fixed candidate BCS, enumerate
  context atoms and incompatibility edges induced by shared variables, then
  solve the finite routing LP/SDP asking whether the three V4 failure sources
  can be assigned to atom ranges with reproduction `5/4` and all compatible
  overlap confined to a bounded list of shared-word curvature terms.  A
  stationary regular solution falsifies that candidate wiring; a strict dual
  certificate supplies the coefficients for `(VGC5)`.

- **Why the scalar restriction is structural, not stylistic.**  The node's own
  requirement that the proof of `(GVC2)` "may not factor through the scalar
  list `(tau(P_c))_c`" is the router row of
  `local-exactification-invariants-cannot-close-gluing-holes`: independent
  local rounding determines each context only up to its own conjugating
  isometry, so the per-context scalar list is precisely the invariant part of
  the data and cannot see a witness manufactured in that direction.  The
  useful consequence is a one-line screening test — a candidate cross-context
  observable is dead as soon as it is checked to be unchanged by independent
  per-context conjugation, before any capacity estimate is attempted.
