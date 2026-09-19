---
rg: 2
id: atlas-a8-index-33-to-89-sp6-classification-proof
kind: route
title: Filter the small-simple order table and inspect the Sp6(2) maximal subgroups
target: atlas-a8-index-33-to-89-is-orthogonal-sp6
requires: []
---

Because `A ~= A8`, Lagrange gives `20160 | |S|`.  The complete finite-simple
order table through `|A10|=1814400`, filtered by this divisibility, is

```text
S             [S:A8]
A8                 1
PSL_3(4)           1  (same order, but nonisomorphic to A8)
A9                 9
PSL_2(64)          13
M22                22
J2                 30
Sp_6(2)            72
A10                90.                              (SIC4)
```

Thus `(SIC1)` leaves only `S=Sp_6(2)`, proving `(SIC2)`.

It remains to ensure that the already screened orthogonal `A8` is not merely
one of several subgroup classes.  Put `H ~= A8` inside `Sp_6(2)` and choose a
maximal subgroup `M` containing it.  By Lagrange, `20160` divides `|M|`.
The ATLAS maximal-subgroup list for `Sp_6(2)` is

```text
U4(2):2,  S8,  2^5:S6,  U3(3):2,  2^6:L3(2),
(2^(1+4) x 2^2):(S3 x S3),  S3 x S6,  L2(8):3.      (SIC5)
```

Order divisibility eliminates every entry except `S8`.  Hence `H<S8`; its
index there is two.  The only index-two subgroup of `S8` is its derived
subgroup `A8`, so `H` is precisely the derived subgroup of this orthogonal
maximal.  The `S8` maximals form one `Sp_6(2)` conjugacy class, and their
derived subgroups therefore do also.  This proves `(SIC3)` and the claim.
