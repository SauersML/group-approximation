---
rg: 2
id: bijective-ca-preserve-uniform-bernoulli-measure
kind: claim
title: Bijective cellular automata preserve the uniform Bernoulli measure over every group
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that is the isomorphism classification of Bernoulli shifts by base entropy, open over nonsofic groups; this is invariance of the uniform product measure under reversible cellular automata, which needs no entropy theory.
artifacts:
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
---

Let `G` be any group, `A` a finite alphabet, `mu` the uniform product measure on
`A^G`, and `tau: A^G -> A^G` a bijective cellular automaton. Then `tau_* mu = mu`.

The inverse is a cellular automaton, so `sigma o pi o tau` is a local permutation
of a finite window for every local permutation `pi`. It therefore preserves
`mu`, and `tau_* mu` is invariant under every local permutation. The only such
probability measure is `mu`. No amenability is used.

For countable `G` the same fact reads: the encoder's conjugation is a unital
*-endomorphism of the quasilocal algebra, and composing it with the unique trace
gives the trace.

**ESTABLISHED 2026-09-12** by `bijective-ca-preserve-uniform-bernoulli-measure-proof`.
Elementary; no priority is claimed.
