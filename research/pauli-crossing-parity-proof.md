---
rg: 2
id: pauli-crossing-parity-proof
kind: route
title: Reduce packet-dressed gauge words to Pauli crossing parity
target: pauli-gauge-word-retains-and-cocycle
requires: []
---

Represent a Pauli label word by its vector in `F_2^2` and its central
two-cocycle.  A `U` occurrence contributes `a e_X`, a `V` occurrence
contributes `b e_Z`, and every fixed packet letter contributes a constant.
The only source of an `ab` term is a crossing of a `U` and a `V` occurrence.

Deleting adjacent `UU` or `VV` pairs changes the number of such crossings by
an even number.  Hence a deletion word reducing to `UVUV` has odd crossing
parity, and its scalar label phase is `J^(ab+ell(a,b))` for affine `ell`.
This proves `(PDC3)`.  Differences between any two such comparisons are
affine; an affine function vanishing at `00,10,01` also vanishes at `11`, so
no finite family isolates only the AND atom.
