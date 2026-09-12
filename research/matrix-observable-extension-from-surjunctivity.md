---
rg: 2
id: matrix-observable-extension-from-surjunctivity
kind: route
title: Surjunctivity makes every encoder isometry unitary, so conjugation is the matrix extension
target: injective-ca-pullbacks-extend-to-matrix-observables
requires:
  - gottschalk-surjunctivity-conjecture
artifacts:
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
---

This is the converse half of `gottschalk-via-matrix-observable-extension`. With
that route it forms a cycle, which is the house encoding of an equivalence; the
cycle warning is intended.

If every group is surjunctive, an injective automaton `tau` is onto. Then the
encoder isometry `V` on finite perturbations is unitary (Section 2 of the
compression artifact), and `Phi = Ad V*` is a unital *-endomorphism of the
quasilocal algebra with a local inverse (Section 4). It extends the diagonal
pullback `f -> f o tau`, which is the prerequisite's conclusion.

So the matrix-observable prerequisite is the goal restated, not a reduction.
`injective-ca-product-trace-zero-one-law` shows the same for every trace-level
weakening of it: for each automaton, each is a zero-one statement equivalent to
surjectivity. A useful replacement must work at logarithmic, per-site scale.
