---
rg: 2
id: binary-leavitt-atomic-return-via-three-row-compiler
kind: route
title: Use lossless moving addresses to instantiate Atomic Morita Return
target: binary-leavitt-atomic-morita-return
requires:
  - binary-leavitt-three-row-atomic-compiler
  - bounded-prototype-rows-imply-atomic-morita-return
  - conjugacy-addressed-opnorm-challenges-are-lossless
---

Apply the three-row compiler to a presentation model whose prescribed
nontrivial `z`-spectral projection is nonzero.  The output lies in that exact
corner and satisfies the AMR rows with the bound `(BAC1)`.

Every prototype word has one fixed finite filling by presentation relators,
and every remote instance is its literal conjugate.  The abstract bounded
prototype theorem therefore converts `(BAC1)` into a modulus depending only
on the presentation defect, not the selected address, coefficient window or
matrix dimension.  This is exactly `binary-leavitt-atomic-morita-return`.

