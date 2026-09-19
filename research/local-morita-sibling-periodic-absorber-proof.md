---
rg: 2
id: local-morita-sibling-periodic-absorber-proof
kind: route
title: Alternate the two tensor Pauli factors by address parity
target: local-morita-sibling-cells-have-a-two-qubit-periodic-absorber
requires: []
---

Take the two Pauli factors and tensor swap from `(LMS1)--(LMS2)`.  Since
appending `0` preserves address parity and appending `1` reverses it,
`(LMS3)` gives `(LMS4)` at every vertex.  The two children are therefore
always `P_0,P_1` in some order.  Their noncentral generators act on different
tensor factors, so they commute; both contain the same scalar `J=-I_K`.
Tensor swap conjugates either factor to the other, proving every local
parent/child equivalence.

Only `P_0` and `P_1` occur as the depth varies.  Hence the same space
`K=C^2 tensor C^2` realizes the entire collection of nodewise relations and
retains the marked central sector at every depth.  This proves the claimed
periodic absorber and the failure of local sibling cells to force growing
capacity.
