---
rg: 2
id: two-outer-row-transvection-proof
kind: route
title: Square-zero commutator of two opposite roots with composable matrix-unit coefficients
target: two-outer-rows-suffice-for-finitary-transvections
requires: []
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

Set `A' = Q_(ac)E_ij` and `B' = Q_(cb)E_ji`.  Since `i != j`,

```text
(A')^2 = Q_(ac)Q_(ac) E_ij E_ij = 0,
(B')^2 = 0,
```
because `E_ijE_ij = 0`.  Next

```text
B'A' = Q_(cb)Q_(ac) E_ji E_ij = (delta_(ba) Q_(cc)) E_jj = 0,
```
using `a != b`, so `Q_(cb)Q_(ac) = delta_(ba)Q_(cc) = 0`.  Finally

```text
A'B' = Q_(ac)Q_(cb) E_ij E_ji = Q_(ab) E_ii.
```

With `(A')^2 = (B')^2 = B'A' = 0` the two elementary matrices `I + A'` and
`I + B'` have inverses `I - A'`, `I - B'`, and

```text
(I+A')(I+B')(I-A')(I-B') = I + A'B' = I + Q_(ab)E_ii,
```
after cancelling every term containing `A'A'`, `B'B'` or `B'A'`.  That is
`(TOR1)`.

Together with the ordinary cross-ray roots `I + Q_(ab)E_ij` (`i != j`),
`(TOR1)` realizes every transvection of the finitary module, so over
`F_2` all of `(TOR2)`: any finite invertible matrix is a product of
elementary row operations, swaps reduce to three additions in
characteristic two, and pivots are `1`.  Conversely each generator is
finitary, so the generated group is exactly `L_n`.

Only the two outer indices `i` and `j` appear; `c` is an inner index of
the coefficient ring.  Hence `n = 2` suffices.
