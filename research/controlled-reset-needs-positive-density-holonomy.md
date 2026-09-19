---
rg: 2
id: controlled-reset-needs-positive-density-holonomy
kind: claim
title: Promote the Schur flip square to positive-density controlled holonomy
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that classifies one controlled Pauli covariance and cancels its multiplicity twist under conjugation; this must couple the twists at positive density.
  schur-packet-flips-realize-predicate-cocycle: that already constructs the exact commuting two-cell and its forbidden projective sign; this must make many finite-dimensional multiplicity fibers pay a normalized-HS density.
  commuting-automorphism-cocycle-forces-multiplicity: that obtains one fixed parity divisor and proves its normalized-HS limitation; this asks for the missing extensive contextual amplification.
  q-masa-to-fresh-packet-morita-bridge: that asks for the completed packet bridge; this isolates its positive-density holonomy gate.
---

Use only the balanced relative-Pauli child halves allowed by
`clifford-groupified-control-is-forced-balanced`.  Pauli-complete every
controlled operation and realize its local conjugation by
`controlled-pauli-corner-has-clifford-groupification`.

For the multiplicity two-cell, use the existing Schur flip square

```text
u b u^(-1)=alpha_P(b),
v b v^(-1)=alpha_Q(b),
[u,v]=1,                                                (PDH1)
```

from `schur-packet-flips-realize-predicate-cocycle`.  On a forbidden packet
simple its spin implementers anticommute, so the external multiplicity
implementers anticommute; on the complete allowed orbit their projective
commutator is trivial.

Construct a finite family of such squares and shared-context relations such
that, in every sufficiently accurate marked matrix microstate:

1. every allowed tracial BCS representation extends and retains the marked
   central sign;
2. a fixed positive density of the unwanted controlled multiplicity fibers
   carries independent projective squares, rather than only one parity
   defect in an arbitrarily large multiplicity space;
3. the density bound uses joint shared-context operator data and vanishes on
   each local Plancherel type vector separately; and
4. the resulting fixed-depth comparison has contraction factor below one
   after every complementary type is included.

The required output is an explicit finitely presented group and a rational,
cross-Gram, or property-`(T)` adjoint certificate for clause 2.  The local
groupification and the projective two-cell are solved.  The remaining theorem
is exactly the promotion from one fixed divisibility condition to extensive
normalized-HS holonomy.

## Attempts

- **Literal corner equality. Dead.** It is excluded by
  `central-corner-block-is-not-a-group-word`.
- **Pauli covariance promotion. Solved.**  The controlled block is an honest
  covariance in every marked representation.
- **Arbitrary selector control. Dead.** A Pauli partner forces the two control
  signs to have equal trace; only the balanced relative child halves survive.
- **Stable-letter spectral data. Dead.**  `CZ tensor V` contains an arbitrary
  multiplicity involution `V`; its trace and spectral projections are not
  representation-uniform.
- **Covariance-only replay. Dead.**
  `clifford-covariance-atlases-have-regular-flow` supplies an exact stationary
  counterrepresentation.
- **Projective flip square. Solved locally.**
  `schur-packet-flips-realize-predicate-cocycle` supplies `(PDH1)`, and
  `commuting-automorphism-cocycle-forces-multiplicity` forces even forbidden
  multiplicity.
- **Fixed parity as the floor. Dead.**  One multiplicity copy can be repaired
  inside a large block at vanishing normalized-HS cost.  This is the same
  amplification fence as `fixed-depth-rank-mesh-has-zero-hs-density`.
- **Positive-density holonomy. Active.**  The live certificates are the
  contextual exit cross-Gram curvature of
  `global-v4-exit-capacity-is-cross-gram-curvature` and the property-`(T)`
  adjoint wall of `schur-wall-in-property-t-compressor-pays-hs-energy`.  Either
  must be coupled to the controlled flip squares before local packet copies
  are separated.

