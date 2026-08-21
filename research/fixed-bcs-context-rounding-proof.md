---
rg: 2
id: fixed-bcs-context-rounding-proof
kind: route
title: Exactify each elementary-abelian context and place Alice on the right
target: fixed-bcs-context-rounding-gives-commuting-strategy
requires:
  - gowers-hatami-finite-group-hs-stability
---

Spectrally round each `U_j` to a self-adjoint involution `B_j`; functional
calculus gives `(BCR2)`.  For a context `c`, its approximate involution and
commutator table is an approximate representation of the fixed finite group
`(C_2)^|c|`.  Finite-group flexible HS stability gives exact commuting
involutions `A_(c,j)` (after the standard negligible flexible corner, absorbed
by amplification) with

```text
||A_(c,j)-U_j||_2<=rho_B(eta),                         (1)
```

where the finite maximum over contexts is effective and tends to zero.

Use the Hilbert space `L^2(M_d,tr_d)` (including the flexible amplification
if needed), with unit vector `1`.  Let Bob's observable be `L(B_j)` and let
Alice's observable in context `c` be `R(A_(c,j))`.  All left actions commute
with all right actions.  The `A_(c,j)` commute within a context, so their
joint spectral projections form Alice's context PVM.

For the consistency check on `(c,j)`, the disagreement probability is

```text
(1-Re tr_d(A_(c,j)B_j))/2
 =||A_(c,j)-B_j||_2^2/4,                              (2)
```

bounded by `(1)` and `(BCR2)`.  Every forbidden projection is a fixed
multilinear polynomial in at most `k` involutions.  Product telescoping
compares its trace on `A_c` with its trace on `U_c` by a fixed multiple of
`rho_B(eta)`; the assumed forbidden mass controls the latter.  Summing `(2)`
and these finitely many losses with the rational question distribution gives
the effective modulus in `(BCR1)`.

