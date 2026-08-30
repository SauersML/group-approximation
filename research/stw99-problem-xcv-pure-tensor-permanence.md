---
rg: 2
id: stw99-problem-xcv-pure-tensor-permanence
kind: claim
title: Minimal tensor products of pure C*-algebras are pure (STW Problem XCV, general part)
root: true
refuted_by:
  - pure-tensor-entangled-compact-counterexample
distinct_from:
  stw99-problem-xcv-cu-z-tensor: that prescribes the entire Cuntz semigroup of the tensor product and is refuted by a compact K-theory cross class; the counterexample tensor remains pure and therefore does not decide this weaker permanence question.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem XCV, general part, of Schafhauser--Tikuisis--White.**  Is the
minimal tensor product of pure C\*-algebras pure?

This remains open.  The counterexample to the first part does not refute it:
both the nuclear Z-stable tensor square and the concrete selfless free-group
tensor square used in `stw95-cu-z-tensor-counterexample` are pure.  Their
failure is finer—the tensor product has extra compact Cuntz classes—not a
failure of almost unperforation or almost divisibility.

## Attempts

The exact/selfless case is positive by tensor-product permanence of
selflessness, and the nuclear Z-stable case is positive by absorption.
Any counterexample must therefore evade those mechanisms; no construction is
currently recorded that makes either almost unperforation or almost
divisibility fail after tensoring.

The current positive and negative frontiers are now explicit.  A splitting
of the canonical abstract-to-concrete Cu tensor map suffices by
`split-cu-tensor-map-implies-pure-product`.  On the other hand, an entangled
compact-bearing irreducible representation would refute the claim through
`pure-tensor-entangled-compact-route`; spatial product representations are
ruled out by `spatial-pure-factor-reps-have-no-joint-compacts`.
