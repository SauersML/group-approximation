---
rg: 2
id: finite-cocycle-source-audit-via-projective-gate-order
kind: route
title: Audit the projective-basis gate before testing torsion and finite Clifford phases
target: current-nonce-sources-do-not-supply-a-finite-cocycle-sector
requires:
  - zero-one-irs-character-is-normal-dirac
  - cdi-wreath-extension-preserves-projective-basis-gate
  - cdi-standard-generator-choice-fails-projective-gate
  - mipstar-does-not-supply-effective-projective-basis
  - twisted-group-basis-forces-affine-context-support
  - cdi-torsionization-needs-schur-multiplier-separation
  - finite-index-projective-core-yields-central-witness
  - primary-nonce-sources-miss-finite-index-core
---

Apply the zero-one lemma to the native IRS character, the exact CDI trace and
phase computation to the wreath envelope, and the affine-context theorem to
the native BCS observables.  Each source stops before a projective regular
basis is available.  Conditional on such a basis, use the Schur-multiplier
criterion `(FCS2)`.  Finally observe that finite Clifford labels live in CE
matrix packets; a finite label grading can only move the problem to its
finite-index kernel, where a non-CE projective core is exactly the missing
primary-source datum.
