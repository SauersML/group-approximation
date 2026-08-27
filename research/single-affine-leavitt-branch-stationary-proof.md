---
rg: 2
id: single-affine-leavitt-branch-stationary-proof
kind: route
title: Apply Bass--Serre residual finiteness to the finite diagonal branch chart
target: single-affine-leavitt-branch-chart-is-stationary
requires:
  - affine-active-doubling-is-elementary-matrix-conjugacy
  - finite-graph-of-groups-representation-types-are-integer-flows
---

Both vertex and edge groups in `(SAB2)` are finite. Standard Bass--Serre
theory makes its fundamental group virtually free; finitely generated
virtually free groups are residually finite. The base embeds by the normal
form theorem, so residual finiteness supplies a finite quotient separating
any chosen nontrivial active element. Its regular permutation representation
is an exact finite-dimensional marked countermodel.

The representation-flow statement is the specialization of
`finite-graph-of-groups-representation-types-are-integer-flows` to the two
embeddings `(SAB1)`.
