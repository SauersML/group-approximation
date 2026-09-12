---
rg: 2
id: three-chart-affine-clifford-return-incidence
kind: claim
title: Three affine Clifford reset cells have one word-level common endpoint marginal
distinct_from:
  derived-lifted-gauge-reset-spin-bridge: that proves the corrected full-character restriction equality for one reset edge; this must couple all three comparison charts so forbidden mass cannot hide in independent multiplicity rotations.
  s3-radical-charts-give-linear-local-hs-payment: that proves payment conditional on three supplied comparison laws with shared endpoint marginals; this must construct those laws as ordinary words in one finite presentation.
  finite-graph-of-groups-representation-types-are-integer-flows: that controls irreducible type counts; the endpoint events here live inside a merged type's multiplicity commutant and are invisible to those counts.
---

For one fixed Fanizza predicate, let `R_1,R_2,R_3` be the three radical-twist
chart groups and let `L_i<=R_i` be their common symplectic reset subgroups.
The corrected affine packet gives an equal-scale edge from every `L_i` to the
same fresh rank-sixteen Schur scale: after a complete semantic character is
fixed, both sides restrict as `2 rho_15`.

The required conclusion is stronger than equality of these restriction
vectors.  Construct a finite presentation in which the three binary endpoint
events used in `(RNS1)` are represented by the **same two projections** in
the fresh multiplicity algebra, up to `O(sqrt(E))` in every finite-dimensional
tuple of relator energy `E`.  If `q` is the forbidden source mass, the three
comparison words must then satisfy

```text
p_00+p_01+p_11 >= q-O(sqrt(E)),                         (TCR1)
```

and their failure masses must be charged to that same relator energy.  The
finite presentation must simultaneously admit the countably amplified exact
HALT representation and embed its marked base.

## Failed common-vertex shortcut

Gluing the three affine reset cells to one fresh finite-group vertex proves
only that they read the same **irreducible type multiplicity**.  On the reset
edge the two radical labels have already merged into one type, so their binary
endpoint event is a projection `P_i` in the multiplicity commutant.  An edge
intertwiner has the form

```text
I_(rho_edge) tensor V_i,
```

and the three unitaries `V_i` are independent.  They preserve the type vector
but replace `P_i` by `V_i P_i V_i^*`.  Thus one common fresh vertex does not
give the common Bernoulli marginals `(RNS1)`.  Stabilizing every old chart by
the same Pauli factor only tensors this counterexample with an identity.

The missing theorem is therefore a multiplicity holonomy or shared-word
constraint which kills those independent commutant rotations in finite
matrices without killing the amplified infinite completeness model.  The
twenty-qubit packet closes the edge-dimension audit but does not supply this
constraint.

## Attempts

- `s3-equivariant-edge-closes-common-marginals` supplies the constraint
  structurally, by closing all three transports into one `S_3`-semidirect
  edge.  The full generated-group and kernel audit is now closed by
  `regular-clifford-edge-map-has-zero-kernel`; the remaining input in
  `s3-equivariant-affine-clifford-return-edge` is the capacity-gated global
  endpoint-word cell.
- `three-chart-return-from-cross-context-relators` supplies it by quotient
  instead: the raw radical basis words are fixed zero-one packet words
  (SER1), so the two `(RNS1)` agreements can be imposed as two explicit
  cross-context conjugation relators `(CCR1)` — equivalently, the two
  comparison loops centralize their shared radical words up to a fixed
  central character.  The events become images of fixed words, so no
  independent rotation exists to kill; the whole burden moves to one
  completeness computation,
  `covariant-model-satisfies-cross-context-radical-relators`.
