---
rg: 2
id: atlas-a8-index-33-to-89-is-orthogonal-sp6
kind: claim
title: The only finite-simple A8 overgroup at indices thirty-three through eighty-nine is the orthogonal class in Sp6(2)
distinct_from:
  atlas-q14-simple-overgroup-index-is-at-least-33: that uses the marked Atlas relations to reach index thirty-three; this is an ambient finite-simple overgroup classification independent of those markings.
  atlas-a4-sp6-packet-collision-screen: that screens one specified orthogonal A8 conjugacy class in Sp6(2); this proves every A8 subgroup in the sole surviving ambient group belongs to that class.
---

Let `S` be a finite nonabelian simple group and `A<S` with `A ~= A8`.  If

```text
33 <= [S:A] < 90,                                   (SIC1)
```

then

```text
S ~= Sp_6(2),       [S:A]=72.                       (SIC2)
```

Moreover `A` is the derived subgroup of a maximal

```text
O_6^+(2):2 ~= S8 < Sp_6(2).                         (SIC3)
```

All such `A8` subgroups form the single orthogonal conjugacy class tested by
`atlas-a4-sp6-packet-collision-screen`.

This is CFSG/ATLAS-dependent.  The order interval uses the complete simple
group order table in the GAP Character Table Library, *Simple Groups by Group
Order* (CTblLib 1.3.8).  The overgroup assertion uses the maximal-subgroup
table for `S_6(2)` in Conway--Curtis--Norton--Parker--Wilson, *Atlas of Finite
Groups* (1985), p. 46.

