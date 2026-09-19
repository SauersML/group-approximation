---
rg: 2
id: paired-frame-fixed-kernel-polynomial-clock-no-go-proof
kind: route
title: Exhaust the twelve polynomial transvections and their two-letter semigroup
target: paired-frame-fixed-kernel-polynomial-clock-no-go
requires:
  - support-packet-paired-word-frame-exposes-forbidden-rank
artifacts:
  - experiments/paired_frame_kernel_polynomial_stabilizer.py
---

Polynomials over `F_2` are represented exactly as coefficient bitsets.  A
polynomial vector belongs to `K tensor F_2[x]` exactly when its coefficient
vector in every degree belongs to the eight-element binary kernel `K`.  The
verifier applies the exterior-square action of each `I+xE_(a,b)` to all eight
kernel vectors and obtains precisely `(PKN1)`.

It then checks every ordered product of two surviving lifts through 64 powers.
The structural reason the reported degree never grows is exact: for surviving
matrix units `E_(a,b)` and `E_(c,d)`, the column indices are odd and the row
indices are even, so `b!=c` and every product is zero.  Hence any sum of them
has square zero and `(I+xN)^2=I`.

The script asserts the exact four-element list, absence of opposite pairs,
and absence of a growing product; it exits successfully only with this
classification.
