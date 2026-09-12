---
rg: 2
id: support-return-chart-intersection-proof
kind: route
title: Close both transported Pauli charts and compute their relative support swap
target: support-return-charts-meet-in-two-pauli-pairs
requires:
  - support-return-gives-gauged-native-loop
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

Close the six same-center Pauli roots by exact prefix-normal-form matrix
multiplication; the result is `E` of order `128`.  Conjugate every matrix
by `W_1` and `W_2` to obtain two exact sets of `128` matrices.  Pairwise
comparison uses faithful prefix equality, so coarse completeness
representations do not create false mismatches.  The sets are unequal and
their exact intersection has `32` matrices.

Independently close the four generators `A_2,A_3,B_2,B_3`.  This gives an
extraspecial two-pair group of order `32`.  Conjugate it by `W_1` (or,
equivalently, by `W_2`); exact set equality identifies the transported
group with `E_1 intersect E_2`, proving `(SCI2)`.

Because `e_000<=e_0`, the two partial swaps commute and their product is
the partial swap on the symmetric-difference projection `e_0+e_000`.
Direct matrix multiplication proves `(SCI3)`.  Conjugating the six
generators of `E` gives the bit row `(SCI4)`.  Conjugating all `128`
elements of `E_1` gives exact set equality with `E_2`, while conjugating
all `32` intersection elements fixes each one.  This proves
`(SCI5)` and the identity-label assertion on the common subpacket.
