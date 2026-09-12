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
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
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

**This criterion is the goal restated (2026-09-12).** For each automaton,
Section 4 of the compression artifact gives onto => extension and Section 5
gives extension => onto. The converse route
`matrix-observable-extension-from-surjunctivity` closes the cycle with
`gottschalk-via-matrix-observable-extension`. That cycle is the house
encoding of an equivalence, so this claim renames the goal rather than
reducing it.

**Trace-level weakenings are restatements too (2026-09-12).** By
`injective-ca-product-trace-zero-one-law`, for each injective automaton the
image measure either equals the uniform measure or is singular to it. Every
state extending the product trace takes the range projection to 0 or 1, and
the compression is tracial, or multiplicative, exactly in the onto case.
Tracial compatibility, positivity of the range projection, and absolute
continuity of the image measure are each equivalent to surjectivity. No trace
inequality can be an intermediate step. A replacement has to count at
per-site logarithmic scale, where the square-alphabet hypothesis acts, and
rectangular sections pass every structural test here without being onto.

**The logarithmic-scale replacement (gk-rokhlin, 2026-09-12).**
`strict-automaton-lowers-bernoulli-rokhlin-entropy` counts at exactly that
scale. A strict encoder with a missing window `Omega` gives the amplified uniform
Bernoulli shifts `(A^k)^G` Rokhlin entropy at most
`k(log q - delta/|Omega Omega^-1|) + log 3`. A per-site saving of order
`q^-|Omega|` at markers beats the fixed marker cost once `k` is large. The
open step is the lower bound: `bernoulli-rokhlin-entropy-maximal-for-every-group`,
equivalently `every-group-has-positive-rokhlin-entropy-action`. No trace-level
premise can replace it.
