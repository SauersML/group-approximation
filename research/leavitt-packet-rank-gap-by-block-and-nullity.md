---
rg: 2
id: leavitt-packet-rank-gap-by-block-and-nullity
kind: route
title: Read the inverse defect from one block and pay the two product nullities
target: leavitt-kernel-packet-has-a-finite-coefficient-rank-gap
requires:
  - leavitt-24k-kernel-packet-excludes-scalar-field-models
artifacts:
  - research/artifacts/leavitt-finite-coefficient-rank-gap-2026-09-08.md
---

Retain `Z=ts` throughout the indexed word calculation. The bottom
right block of `r_*-I` is `Z-I`, while
`R_v=x_13(v^2+Z)` and `R_0=x_12(tvsZ^2)`. Write
`r=rank(Z-I)`, `q=rank(v^2+Z)`, and `p=rank(tvsZ^2)`.
Then `rank v>=d-r-q`, `nullity t<=r`, and
`nullity(sZ^2)<=r`: for the last inequality, `sZ^2` is injective
on `ker(Z-I)`. The product rank inequality gives `p+q+3r>=d`.
The displayed block bounds `r` by `rank(r_*-I)` and yields the
claim after normalization by `3d`.

For exact solutions over a directly finite ring, the same block
forces `ts=1`, hence `st=1`. The other two words force `v^2=1`
and `tvs=0`; multiplying the latter by `s` and `t` forces `v=0`,
a contradiction in a nonzero ring. The artifact contains the full
block multiplication and the scope restriction.
