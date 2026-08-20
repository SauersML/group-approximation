---
rg: 2
id: fanizza-shared-multiplicity-predicate-circuit-cell
kind: claim
title: Cancel multiplicity commutators in one reversible cell for the three Fanizza predicates
artifacts:
  - research/artifacts/reverse-kleene-multiplicity-holonomy-audit-2026-08-20.md
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for an exact BCS representation in a positive canonical group corner; this permits arbitrary infinite HALT completion and asks only for a finite-matrix decoder estimate.
  shared-context-pairwise-antiphase-v4-routing: that tries to label every failure branch by pair-specific Clifford phases; this computes the fixed nonlinear predicates by reversible gate commutators and targets their external multiplicity residue directly.
---

For the three fixed nonlinear truth-table shapes in
`fanizza-final-bcs-has-fixed-nonlinear-menu`, construct one fixed finitely
presented reversible Pauli/Schur cell with the following properties.

1. In the HALT GNS model, after countable amplification, all cell relations
   have an exact representation and the native word `d_m=x_(D,m)` remains
   nonidentity.  No trace-preserving extension is required.
2. Every sufficiently accurate finite-dimensional unitary model can be
   exactified on its finite packet sectors so that the conditional-gate
   implementers used in each predicate circuit have commuting external
   multiplicity factors.  Equivalently their residual commutators in `(CPM4)`
   have dimension-independent Hilbert--Schmidt bounds by the defining relator
   energy.
3. Reading the commutator phases with `(CPM2)` and resetting between contexts
   yields, for computable finite constants `A_m,B_m`, the decoder estimates
   `(NSG1)--(NSG2)` without globally centralizing the shared BCS variables.

The difficult point is clause 2.  Different controlled gates naturally have
independent factors `R,T` in `(CPM3)`.  Simply identifying the implementers
may also identify their selector actions and destroy the nonlinear context.
The cell must impose commuting or common multiplicity factors while retaining
distinct spin/selector controls.  A relation `[u,v]=h` is admissible only when
the induced packet automorphism commutator is the inner automorphism of the
chosen packet word `h`; this is the first finite-group consistency test.

This target is finite and machine-independent.  Once it is proved, the linear
Fanizza flattening gadgets contribute only computable telescoping constants,
and the reverse-Kleene route closes without a runtime-uniform modulus.

## Attempts

- **Dress one shared implementer by packet words. Fenced for the basic Pauli
  cell.**  This would make the two external factors in `(CPM4)` literally
  equal.  However
  `packet-dressed-shared-implementer-requires-one-outer-class` proves that
  packet-dressed copies of one stable letter can implement only automorphisms
  in one class of `Out(B)`.  The standard controlled-X and controlled-Z/CZ
  covariances have different actions on the Pauli quotient, hence different
  outer classes.  A larger packet with same-outer-class nonlinear lifts
  remains possible.

- **Independent covariance implementers: fails exactly.**  Schur's lemma
  leaves factors `R,T` on the external multiplicity space, and `(CPM4)` shows
  that their uncontrolled commutator multiplies the intended predicate phase.
- **Identify the two implementers: overconstrains the controls.**  Literal
  equality cancels the multiplicity factor, but can also identify the induced
  selector actions and erase the distinction between the two Boolean inputs.
- **Prescribe `[u,v]=h`: finite consistency test open.**  Before such a
  relation can be used, the packet automorphisms must satisfy
  `[alpha_u,alpha_v]=Ad_h`.  Enumerating a finite packet and words `h` with
  this property is the first exact search; no suitable cell is known yet.
- **One shared multiplicity implementer: algebraically sufficient.**  If the
  different packet actions can be realized as `C_i tensor V` with the same
  `V`, every pairwise commutator loses the multiplicity factor.  The missing
  construction is to force this common factor using ordinary group relations
  without equating the distinct packet actions.
