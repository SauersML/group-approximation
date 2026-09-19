---
rg: 2
id: mf-hyperlinear-of-finite-normal-quotient-proof
kind: route
title: Split the elements across the finite kernel and the quotient
target: mf-hyperlinear-of-finite-normal-quotient
requires: [hyperlinear-elementwise-visibility, mf-finite-normal-tracially-visible]
---

## Why sufficient

By `hyperlinear-elementwise-visibility` it suffices to make every `g != 1`
in `G` tracially visible with a constant depending only on `g`.

*Case `g in N`.*  `N` is a finite normal subgroup of the MF group `G`, so
`mf-finite-normal-tracially-visible` gives visibility with
`c_g=c(N)/(2|N|)`.

*Case `g not in N`.*  The image of `g` in `G/N` is nontrivial, and `G/N` is
hyperlinear, so by the necessity half of `hyperlinear-elementwise-visibility`
the image is tracially visible with constant `1/2`.  Pulling a model of
`G/N` back along the quotient map preserves the multiplicative defect and
the trace, so `g` is tracially visible in `G` with `c_g=1/2`.

Both cases give a constant independent of the finite set and the tolerance,
so `hyperlinear-elementwise-visibility` applies.  End proof.

## Remark

Finite generation is not used.  The literature statement
(arXiv:2508.17392v3, Proposition 1.6) assumes it, presumably because its
proof follows the Deligne-type template of that paper's Theorem 1.3, which
compresses to the negative spectral corner of a single central involution.
The isotypic-corner argument behind `mf-finite-normal-tracially-visible`
handles an arbitrary finite normal subgroup directly and gives the sharper
elementwise conclusion.
