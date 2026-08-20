---
rg: 2
id: dyadic-splitter-from-adaptive-all-pairs-replica-table
kind: route
title: Exactify one supercritical replica table with a universal finite-group stability constant
target: constant-hs-groupification-of-residual-dyadic-splitter
requires:
  - adaptive-all-pairs-schur-replica-table-compiler
  - approximate-schur-replicas-force-exponential-dimension
---

The compiler chooses the replica count at the current residual dimension and
supplies the all-pairs approximation with a fixed error and surviving sign.
The robust exponential-dimension theorem makes its low-energy branch
impossible by `(ASE2)`--`(ART1)`.  Its remaining branches pay the universal
energy floor.  Interpreting the exactified replica cocycles as independent
Pauli splits gives precisely the adaptive dyadic splitter target.

