---
rg: 2
id: huge-elementary-abelian-two-group-is-not-sequential-operator-mf
kind: claim
title: A sufficiently large elementary abelian two-group is not sequentially operator-MF
distinct_from:
  property-t-free-leavitt-full-mf-radical: that is the open countable finite-presentation target; this is an unconditional cardinality obstruction for an uncountable group under the unrestricted formal predicate and does not address the countable problem.
  orthogonal-root-self-copy-is-mf-compatible: that is a countable locally finite calibration admitting sequential models; this group is too large for any single sequence of matrix coordinates despite being locally finite and residually finite.
artifacts:
  - GroupApproximation/Sofic/OperatorMF.lean
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

Let `I` be a set with

```text
|I|>continuum
```

and put

```text
E_I=directSum_(i in I) C_2.
```

Then `E_I` does not satisfy the unrestricted sequential predicate
`IsOperatorMF`.  Moreover `E_I` is:

1. abelian and of exponent two;
2. locally finite and amenable;
3. residually finite;
4. without property `(T)`.

The failure of sequential operator-MF is purely a width obstruction.  In
particular, outside countability, residual finiteness and exact finite models
for every finite subset do not imply embeddability into one countable matrix
corona.

