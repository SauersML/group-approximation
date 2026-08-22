---
rg: 2
id: leavitt-long-odd-face-partitions-proof
kind: route
title: Spend the 24 face corners after excluding odd relations through nine
target: leavitt-long-odd-face-core-partitions
requires:
  - leavitt-no-odd-nine-corner-relations
---

The six face lengths sum to `24`.  There is exactly one odd internal face
and the outer face is odd.  The other four internal faces are even and at
least two.  For internal odd length `d` and outer odd length `d_0`, partition
`24-d-d_0` into four even positive integers.  For `d=11,13,15` this gives
exactly `(LOP1)` and nothing else.

A length-two internal relation is necessarily one of the four involution
gates by the short corner census.  The standard digon contraction deletes
its two incident cubic vertices and joins their remaining half-edges,
reducing `V` by two and `F` by one.  The stated core sizes follow.

