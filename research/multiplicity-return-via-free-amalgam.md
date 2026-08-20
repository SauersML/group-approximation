---
rg: 2
id: multiplicity-return-via-free-amalgam
kind: route
title: Replace stationary finite type flow by a contractive infinite Bass-Serre transfer
target: multiplicity-return-transducer
requires:
  - countable-tracial-amalgam-extension
  - schur-marked-character-transfer-gap
  - bass-serre-schur-transfer-contraction
  - symmetrized-reset-collapses-schur-flow-to-one-ray
  - non-ce-bcs-has-robust-approximate-energy-gap
  - predicate-rank-gate-doubles-restriction-multiplicity
  - marked-hs-separation-forces-spectral-density
  - bounded-overlap-syndrome-energy-accounting
  - perron-frobenius-branching-carrier-collapse
---

Use a fresh free factor for each packet stage and amalgamate only over the
finite multiplicity wire.  The first prerequisite extends the exact tracial
model indefinitely and makes selector renewal structural.  The reset removes
all stationary directions except one scalar current, while the Bass--Serre
contraction prevents that current from circulating without loss.

The robust BCS gap forces positive rank-jump traffic.  Contractive transfer
then says this traffic either escapes, contradicting the fixed marked-carrier
floor, or leaks into a bounded-overlap family of relator defects.  The
Perron--Frobenius carrier-collapse endpoint converts the latter into a uniform
HS energy floor.  This supplies all five clauses of the target without
asserting that a finite graph of finite groups can be nonhyperlinear.
