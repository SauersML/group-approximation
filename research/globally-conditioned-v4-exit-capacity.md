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

The exact non-CE tracial BCS model must extend to a representation witnessing
`w!=1`; this is the completeness half.  On finite-dimensional microstates,
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
- **Independent local exactification is insufficient.**  Choosing a separate
  Gowers--Hatami correction for every packet gives unrelated conjugating
  isometries and leaves the cross-Gram matrix unconstrained.  The branch maps
  must be extracted from the original shared-word tuple first, or from one
  simultaneous correction on an overlap complex.
- **Deferred finite computation.**  For a fixed candidate BCS, enumerate
  context atoms and incompatibility edges induced by shared variables, then
  solve the finite routing LP/SDP asking whether the three V4 failure sources
  can be assigned to atom ranges with reproduction `5/4` and all compatible
  overlap confined to a bounded list of shared-word curvature terms.  A
  stationary regular solution falsifies that candidate wiring; a strict dual
  certificate supplies the coefficients for `(VGC5)`.
