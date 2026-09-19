---
rg: 2
id: unitary-blr-polar-self-correction-proof
kind: route
title: Polarize the unitary BLR difference cocycle
target: unitary-blr-average-self-corrects-uniformly
requires: []
---

Define the right-difference corrector

```text
C_x(y)=f(x+y)f(y)^*.                                         (UBP1)
```

For fixed `x`, insert a fresh uniform `z`.  Bi-invariance of normalized HS
distance and two BLR errors give

```text
||C_x(y)-C_x(y+z)||_2
 <=||f(y)f(z)-f(y+z)||_2
   +||f(x+y)f(z)-f(x+y+z)||_2.                               (UBP2)
```

Both pairs in `(UBP2)` are uniform when `(y,z)` is uniform, even with `x`
fixed.  Since `(y,y+z)` is also uniform on `A^2`,

```text
sup_x E_(y,w)||C_x(y)-C_x(w)||_2^2 <=4 delta^2.               (UBP3)
```

Let `M_x=E_y C_x(y)` and let `P_x=polar(M_x)`, with an arbitrary unitary
extension on the kernel.  The unitary variance and polar inequalities used in
`(NC17)--(NC19)` imply from `(UBP3)` that

```text
sup_x E_y||P_x-C_x(y)||_2^2 <=4 delta^2.                      (UBP4)
```

Also

```text
E_(x,y)||C_x(y)-f(x)||_2^2=delta^2.                           (UBP5)
```

Minkowski in `L^2(x,y;M_d)` applied to `(UBP4)--(UBP5)` proves
`(UBA2)`.

The endpoint uses the exact, noncommutative-safe cocycle cancellation

```text
C_x(z+y) C_z(y)=C_(x+z)(y).                                  (UBP6)
```

For fixed `x,z`, replace the three terms in `(UBP6)` by their polar means.
Each replacement has RMS at most `2 delta` by `(UBP4)`, so triangle inequality
gives

```text
||P_xP_z-P_(x+z)||_2 <=6 delta.
```

No commutation or spectral rounding is used.  This proves `(UBA3)`.

