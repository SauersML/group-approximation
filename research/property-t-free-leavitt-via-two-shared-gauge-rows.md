---
rg: 2
id: property-t-free-leavitt-via-two-shared-gauge-rows
kind: route
title: Reblock the root and contradict two affine gauge-rank equations
target: property-t-free-leavitt-full-mf-radical
requires:
  - torsion-normal-generator-has-full-support-corona-core
  - binary-leavitt-two-shared-gauge-selector-compiler
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - full-leavitt-idempotent-defect-saturation
---

Assume a norm-matrix-corona representation keeps `z` nontrivial.  Reblock
with `torsion-normal-generator-has-full-support-corona-core`; the rounded
nontrivial `z` sector then has normalized mass bounded below by a fixed
constant.  Apply the two-shared-gauge compiler on that active core.

If the two selector-row defects tend to zero, `(TSG3)` makes the common
gauge fraction `theta` tend both to `1/2` and to `5/6`, which is impossible.
The positive carrier mass prevents this fixed corner contradiction from
being diluted in the ambient normalized trace.  Hence the corona
representation kills `z`.  Finally
`full-leavitt-idempotent-defect-saturation` normally generates every root
from `z`, so the MF radical is all of `Delta`.

No property `(T)`, Kazhdan projection, global coefficient module, sparse
atom return, or literal controlled reflection occurs in this route.

