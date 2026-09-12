---
rg: 2
id: lin-global-gauge-covariance-proof
kind: route
title: Follow the common extraction isometry through Read, Hide, Sample, and Intro
target: lin-introspection-payload-is-global-gauge-covariant
requires:
  - generator-column-pauli-test-globalizes-but-does-not-pin-sites
---

The source-level proof of Lin's Theorem 7.3 first restricts a near-optimal
strategy to the Pauli-basis subtest and obtains `V_A,V_B`.  It explicitly
defines `(LGC1)` for **every** introspection question, not only the Pauli
questions, and observes that the strategy on the conjugated state and all
the conjugated measurements has the same value up to the state-extraction
error.  Synchronization/orthogonalization is then performed in this common
gauge.  The proof's next strategy changes only `(Pauli,W)` to the standard
Pauli measurement.  The remaining cross-edges charge the replacement to
`Gen Pauli`, `Hide`, `Read`, `Sample`, and `Intro` in sequence.  Hence no
payload observable is compared with an unconjugated old-frame operator.

For the sampler correction, a uniform index is itself a linear seed.  The
typed sampler need not map that seed linearly to the length-`n` column: just
as Lin's source invokes an encoding routine after sampling its short code
message, the corrected verifier invokes the explicit generator-column
lookup.  Bounded duplication changes each atom weight by only a universal
factor, preserving a constant Poincare bound.

The last paragraph is a syntactic separation.  Classical parity evaluation
does not create a group word or a van Kampen diagram.  Thus the gauge-
covariant game proof removes the site-localization requirement but leaves
the word-oracle claim unchanged.

