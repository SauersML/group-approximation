---
rg: 2
id: fanizza-fixed-nonlinear-menu-has-small-rank-gates-proof
kind: route
title: Exhaust the bounded variable orders and verify every Schur rank
target: fanizza-fixed-nonlinear-menu-has-small-rank-gates
requires:
  - fanizza-final-bcs-has-fixed-nonlinear-menu
  - ordered-bdd-compresses-predicate-rank-gate
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
---

The script encodes the three truth tables exactly as in `(FNM1)`.  For each
variable order it constructs the reduced ordered decision diagram, converts
it to `(BDD1)`, evaluates the affine matrix on the full Boolean cube, and
checks

```text
rank_F2 M(x)=baseline+failure(x).
```

There are only `720` orders in the largest case and `64` assignments per
order.  The exact MSI run on one low-priority core returned `(FSG1)` and also
verified that a single forbidden atom of arity `k<=6` has BDD baseline `k+1`.
The packet order and simple dimensions then follow directly from the
Schur--Clifford class-two-group construction.
