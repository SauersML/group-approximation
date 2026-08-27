---
rg: 2
id: groupify-raw-radical-violation-chart
kind: claim
title: Reset and transport the raw radical branches of a forbidden atom
distinct_from:
  groupify-schur-child-center-chart: that must expose a selector-controlled inverse-column coefficient of the rank-up compiler; this starts with two fixed group words which already label every rank-drop child on its forbidden atom.
  branch-controlled-pauli-selector-reset: that balances branches of a raw word commuting in the whole shared abelian subgroup; here the radical words commute with the packet only after restriction to their forbidden selector atom.
---

For every fixed predicate packet in
`boolean-violation-is-one-raw-radical-qubit-drop`, construct a finite ordinary
group chart which, on each forbidden selector atom `a`, does the following.

1. It recognizes the four child types by the signs of the raw words
   `P_a,Q_a` in `(BRD8)`.
2. It exactifies and balances their weighted multiplicities with loss at most
   `C sqrt(E)`, without requiring `P_a,Q_a` to centralize satisfying sectors.
3. It resets the old selector chart and transports each resulting child to
   the next context at one fixed packet scale.
4. Its amalgam with the marked BCS base has an exact representation retaining
   the nonidentity marked word.

Unlike `(RSC2)`, no nonlinear selector-controlled group-algebra involution
has to become a group word.  The remaining conditionality is only the fixed
central atom on which two already named words become radical.

## Attempts

- Unconditionally adjoining dual Pauli partners to every packet generator
  gives a nondegenerate hyperbolic completion and balances all radical
  characters, but its restriction is the twisted regular representation.
  A finite HNN return then conserves total dimension and erases the desired
  factor-two copy surplus.
- The active attack is a four-branch failure-block atlas: use the forbidden
  selector atom only as a Hilbert-space carrier, apply the existing rank-one
  endpoint transport separately to the four raw sign pairs, and charge mass
  leaving that atom to the robust BCS syndrome energy.
- **Local chart solved.**
  `three-radical-twist-crossed-products-have-uniform-scale` constructs three
  conjugate ordinary finite groups whose sector algebras are uniformly
  `M_D direct_sum M_D`; on a forbidden atom they implement the three pairings
  of the four raw branches.  The remaining input in
  `raw-radical-chart-via-s3-crossed-products` is only the one-sided return of
  those two fixed-scale types to a fresh BCS context.
- The transport half is now exact and quantitative in
  `hnn-transports-forbidden-radical-atom-types`. The remaining operation is
  isolated as `raw-radical-branch-morita-reset`: force the four transported
  orthogonal branches to add as copies of one next fixed-scale packet rather
  than overlap in a stationary Bass--Serre flow.
