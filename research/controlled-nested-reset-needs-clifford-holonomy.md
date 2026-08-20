---
rg: 2
id: controlled-nested-reset-needs-clifford-holonomy
kind: claim
title: Complete the controlled reset by Clifford covariance and multiplicity holonomy
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that classifies one completed controlled Pauli block and cancels its multiplicity twist under conjugation; this must couple several such twists by a non-Bass--Serre relation.
  q-masa-to-fresh-packet-morita-bridge: that asks for the completed positive-density packet bridge; this isolates its exact ordinary-group and multiplicity-holonomy gate.
  clifford-covariance-atlases-have-regular-flow: that rules out a finite graph made only of covariance edges; this asks for the additional two-cell which breaks that stationary flow only on the joint contextual datum.
---

Give the constant-depth controlled nested reset as a finite list of Pauli
generators and controlled operations.  Replace every occurrence of

```text
(1-c)+cu
```

by the stable letter of a Pauli-completed CZ or CNOT semidirect product.  Use
each stable letter through its representation-uniform conjugation action on
Pauli words, so the arbitrary multiplicity involution from `(CPC4)` cancels
from every local covariance calculation.

Then add an explicit finite family of two-cell relators among the stable
letters and shared packet words such that:

1. every allowed tracial BCS representation extends and retains the marked
   central sign;
2. on finite-dimensional marked microstates, the two-cell holonomy acts on
   the external multiplicity spaces and its defect bounds a fixed positive
   density of the unwanted controlled types;
3. the bound depends on the joint shared-context operator data and vanishes
   on each local Plancherel type vector separately; and
4. the resulting fixed-depth comparison has a contraction factor below one
   after every complementary type is included.

The required output is an explicit finitely presented group and a rational
or spectral positive-density certificate for clause 2.  A complete finite
vertex/edge restriction table is not enough:
`clifford-covariance-atlases-have-regular-flow` supplies its exact stationary
counterrepresentation.

## Attempts

- **Literal corner equality. Dead.** It is excluded by
  `central-corner-block-is-not-a-group-word`.
- **Pauli covariance promotion. Solved.**
  `controlled-pauli-corner-has-clifford-groupification` makes the controlled
  Pauli conjugation exact in every marked representation.
- **Stable-letter spectral data. Dead.**  The two extensions
  `CZ tensor V` are both honest representations.  Any trace, spectral
  projection, or branch label read from the letter sees the arbitrary
  multiplicity involution `V`.
- **Covariance-only replay. Dead.**  Any finite composition of semidirect
  packets, amalgams, and automorphism HNN edges has the regular stationary
  flow of `clifford-covariance-atlases-have-regular-flow`.
- **Multiplicity holonomy. Active.**  The remaining finite search is for one
  relation among at least two covariance stable letters whose commutator or
  two-cell boundary is trivial in the exact allowed tracial model but has a
  property-`(T)` adjoint or cross-Gram density floor on the forbidden
  multiplicity correlation.

