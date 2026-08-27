---
rg: 2
id: atlas-left-ideal-nonwandering-proves-compactness
kind: route
title: Quotient a low-rank repeated-natural module by its proper relator-ideal image
target: atlas-augmented-rank-zero-set-compactness
requires:
  - atlas-left-ideal-rank-nonwandering
  - atlas-defect-orbit-span-quotient-dichotomy
---

Apply `atlas-left-ideal-rank-nonwandering` to a sequence in `(ARC1)`.  The
sum of the thirteen residual images has normalized dimension tending to
zero, and `(LRN2)` gives `dim(I E_n)/dim(E_n)->0`.  Hence `I E_n` is proper
for every sufficiently large `n`.

The orbit-span in `atlas-defect-orbit-span-quotient-dichotomy` is exactly
`I E_n`: right coefficients do not enlarge a relator image because every
chart word acts invertibly on the input, while left coefficients generate
its orbit.  The quotient `E_n/I E_n` is therefore a nonzero exact
`Gamma_+`-module whose two chart restrictions are faithful repeated natural
modules.  This is an exact finite binary zero of `E_+`, proving `(ARC1)`.

