---
rg: 2
id: same-center-whitehead-transport-gauge-extraction-proof
kind: route
title: Remove the canonical adjacent swaps inside the exactified three-qubit label algebra
target: same-center-whitehead-gram-extracts-transport-gauges
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - opnorm-packet-exactification-is-dimension-free
---

The normal forms `(SCW4)` identify the two restrictions as
`A_i tensor V_i`.  Since `A_i` lies in the recovered finite label matrix
algebra, left multiplication by `A_i^* tensor I` proves `(WGE2)` exactly.
Multiplication by either fixed label reflection acts only in that same
matrix factor and proves `(WGE3)`.

For an operator-norm microstate, exactify the fixed Pauli packet and use the
fixed-word conjugation tables for the two Whitehead words.  All corrections
involve a fixed finite list, so the error in `(WGE1)--(WGE3)` is `o(1)` with
constants independent of the ambient matrix dimension.  This calculation
never identifies a selector support projection, which is why its conclusion
stops before the native occurrence claim.
