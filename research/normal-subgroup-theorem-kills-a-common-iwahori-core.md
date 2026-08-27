---
rg: 2
id: normal-subgroup-theorem-kills-a-common-iwahori-core
kind: route
title: Promote a two-vertex normal core to the S-arithmetic amalgam and contradict infinite index
target: iwahori-edge-has-no-common-finite-index-normal-core
requires: []
---

Assume `E <= D` is infinite, finite-index in `D`, and normal in both `C` and
`C'`.  The Bass--Serre presentation gives `A=<C,C'>`, so `E` is normal in
`A`.  The S-arithmetic normal-subgroup theorem for the irreducible lattice
`SL_2(Z[1/p])` says that every infinite noncentral normal subgroup has finite
index.  The subgroup `E` is infinite and cannot be central, hence `[A:E]` is
finite.

But `[C:D]=p+1` and `[D:E]` is finite, so `E` has finite index in `C` and is
contained in `C`.  If `[A:E]` were finite, then `[A:C]` would also be finite.
This is false: the distinct vertices on the `SL_2(Q_p)` Bruhat--Tits tree
give infinitely many cosets of `C` in `A` (equivalently the powers of the
denominator element leave every fixed integral coset).  Contradiction.

