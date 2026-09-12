---
rg: 2
id: fixed-bcs-context-rounding-gives-commuting-strategy
kind: claim
title: Fixed-context HS rounding gives a genuine commuting-operator BCS strategy
distinct_from:
  near-perfect-bcs-strategy-gives-synchronous-relator-state: that extracts an approximate relator state from an existing strategy; this constructs a strategy from one finite matrix tuple after local context rounding.
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies one fixed finite group table; this assembles the separately exactified context tables with one globally rounded Bob observable by the left-right GNS representation.
---

Fix a finite BCS `B` on involutions `x_1,...,x_s`, with context sizes bounded
by `k`.  Suppose a tuple of matrices `U_j` has involution defect,
within-context commutator defect, and forbidden-polynomial mass at most
`eta`.  Then one can effectively construct a commuting-operator strategy
`S_eta` for `B` with

```text
1-win(S_eta)<=omega_B(eta),                            (BCR1)
```

where `omega_B(eta)->0` effectively and is independent of matrix dimension.
Moreover Bob's observable for variable `j` is an exact involution `B_j` with

```text
||U_j-B_j||_2<=nu_B(eta),                              (BCR2)
```

for an effective `nu_B(eta)->0`.

The construction does not assert that the separately rounded context tables
commute with the `B_j` on the original matrix space.  Instead, on
`L^2(M_d,tr_d)`, Bob uses left multiplication by `B_j`, Alice uses right
multiplication by the exact commuting table for her context, and the shared
unit vector is `1`.  Left and right multiplication commute exactly.

