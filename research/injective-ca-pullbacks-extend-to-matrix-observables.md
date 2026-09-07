---
rg: 2
id: injective-ca-pullbacks-extend-to-matrix-observables
kind: claim
title: Injective full-shift pullbacks extend to unital homomorphisms on full matrix observables
distinct_from:
  gottschalk-surjunctivity-conjecture: this is the unresolved full-matrix extension criterion, equivalent to the positive goal by the explicit matrix-unit obstruction.
  injective-ca-admit-countable-transitive-decoder-fiber: that seeks one countable classical decoder fiber; this seeks a multiplicative extension of a diagonal observable map.
artifacts:
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
---

For every infinite group G, finite nonempty alphabet A, and injective
cellular automaton tau:A^G -> A^G, the diagonal pullback
f -> f composed with tau extends to a unital *-homomorphism of the
quasilocal A-spin algebra into itself. No locality of this extension is
required in the claim.

This is an OPEN criterion, not a consequence of classical locality.

## Attempts

Quantizing the encoder on finite perturbations gives an isometry V and
an always-local unital completely positive map Phi(O)=V*OV. The ordered
memory calculation is proved in the artifact. It does not prove
multiplicativity: if tau is strict, a local unitary has multiplicative
defect exactly one under Phi.

Forward conjugation O -> VOV* also fails to provide a local homomorphism
with the required unit. In the strict case its value at the identity is
a projection at distance exactly 1/2 from the quasilocal algebra.

Even allowing a different extension has not resolved the problem.
Section 5 proves that a missing output cylinder obstructs ANY unital
homomorphism extension, through the finite matrix-unit identities.
Existence of such an extension therefore cannot be asserted without
settling the original surjectivity question. Lattice quantum-reversibility
results do not provide that all-group existence theorem.
