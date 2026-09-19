---
rg: 2
id: sparse-pauli-random-order-blr-proof
kind: route
title: Count balanced bad faces and use the Pauli symplectic commutator
target: sparse-pauli-pair-defeats-random-order-blr
requires: []
---

Let `A_t` be the set of original rows containing coordinate `t`; then
`|A_t|<=D` and `A_1 intersect A_2=empty`.  Among the `M^2` repeated original
faces, only `O(DM)` contain coordinate `1` or `2`.  Among pair-sum faces, the
number whose symmetric-difference support contains either coordinate is at
most

```text
|A_1|(M-|A_1|)+|A_2|(M-|A_2|)=O(DM).                     (SPR1)
```

Every nonzero parity defect in `(SPB1)` has squared normalized-HS norm at
most `4`.  This proves parity energy `O(D/M)`.  A face is internally
noncommuting only if its support contains both coordinates.  Since the
incidence sets are disjoint, only pairs with one row in `A_1` and one in
`A_2` do this, giving `O(D^2)` faces and commutator energy `O(D^2/M^2)`.

For any ordered-product section there is a sign `epsilon(a) in {+1,-1}`
such that

```text
f(a)=epsilon(a) X^(a_1) Z^(a_2).                          (SPR2)
```

Consequently

```text
f(a)f(b)=(-1)^(a_1 b_2+a_2 b_1) f(b)f(a).                (SPR3)
```

When the exponent in `(SPR3)` is one, put `U=f(a)f(b)` and `W=f(a+b)`.
The two directional BLR defects compare `W` with `U` and `-U`, so the
parallelogram identity gives

```text
||U-W||_2^2+||-U-W||_2^2=4.                              (SPR4)
```

For uniform `a,b`, the symplectic form on their first two bits is nonzero
with probability `6/16=3/8`.  Averaging `(SPR4)` and using symmetry under
`a<->b` yields `(SPB3)`.  The argument is pointwise in a random seed, so it
also survives random choice of the complete ordering table.  Equation
`(SPB4)` follows by averaging the two equally likely relative orders of
`X,Z`.

