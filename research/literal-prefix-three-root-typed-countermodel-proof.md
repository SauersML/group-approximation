---
rg: 2
id: literal-prefix-three-root-typed-countermodel-proof
kind: route
title: Realize the prefix swap between equal typed leaves while keeping the packet identities distinct
target: literal-prefix-three-root-swap-retains-typed-carriers
requires: []
---

Let `E,F` be two copies of one nonzero finite-dimensional Hilbert space and
choose a unitary `x:E->F`, with `y=x^*`.  Then `yx=1_E`, `xy=1_F`, and the
three elementary block matrices multiply to the involution swapping `E` and
`F`.  Place `E` as one diagonal leaf in an exact `M_2` matrix-unit system on
`E direct_sum E`, and place `F` as one diagonal leaf in an exact `M_4`
matrix-unit system on `F^(direct sum 4)`.  These packet identities are
different projections, so their minimal leaves may have equal rank without
contradicting the two-versus-four trace ledger.  Every displayed typed
Morita and three-root identity is exact.

Consequently those relations do not imply a common packet identity.  If that
identity and the supported carrier-conjugacy row are added, `(UBL7)` of
`unitary-offdiagonal-block-gram-is-support-leakage` gives the stated trace
collapse.  The controlled-Z multiplicity twist described in the claim shows
why covariance-only Clifford groupification does not add this row.

