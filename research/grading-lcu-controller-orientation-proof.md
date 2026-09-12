---
rg: 2
id: grading-lcu-controller-orientation-proof
kind: route
title: Expand the zero corner and classify the two control blocks
target: grading-zero-corner-does-not-orient-controlled-payload
requires:
  - central-corner-block-is-not-a-group-word
  - controlled-reflection-cell-has-free-orientation
  - twisted-regular-predicate-projections-have-positive-trace
---

Using `J=-1`, equation `(GAB1)` says `ZW=-WZ`.  Hence

```text
qWq=(1/4)(W-ZW-WZ+ZWZ)=0.
```

For the controller classification, diagonalize `Z` and let `X` exchange its
two eigenspaces.  Commutation with `Z` gives `C=diag(A,B)`.  The standard
covariance relation `CXCX=U` (with involutive, commuting payload) gives
`AB=BA=U`; thus `B=AU` and `A` is an arbitrary commuting involution.  This is
`(GAB3)` and is precisely the free-orientation theorem.

An LCU product uses the actual blocks of each controller, so the factors
`A` enter its supposedly selected corner.  Anticommuting `A` with another
grading makes its diagonal compression zero; commuting does not fix its
sign.  Finally, a universal tracial deletion of the unwanted signed sector
contradicts the positive twisted-regular trace of its predicate projection.
This proves the boundary and leaves only the finite-matrix-specific option
in `(GAB4)`.
