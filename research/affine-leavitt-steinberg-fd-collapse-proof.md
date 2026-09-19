---
rg: 2
id: affine-leavitt-steinberg-fd-collapse-proof
kind: route
title: Intersect the finite torsion-root kernels and apply the active module doubling law
target: affine-leavitt-steinberg-mark-is-fd-invisible
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

The finite-presentation and property-`(T)` inputs are the pinned
Krstic--McCool and Ershov--Jaikin-Zapirain theorems already source-verified in
`research/artifacts/atlas-relator-extraction-2026-08-15.md`.  Nontriviality of
the root follows after mapping to the elementary matrix group.

For a finite-dimensional unitary representation, simultaneous
diagonalization makes each additive exponent-`p` root image finite.  The
intersection of the twenty root kernels has finite additive index.  Two
spare Steinberg indices multiply this kernel on the left and right, so every
root over the generated two-sided ideal `I` dies.  Since `k` is finite,
`R_A/I` is a finite ring.

In that quotient, right multiplication on the finite set `A(R_A/I)` gives a
bijection with two disjoint copies of itself via the relative Leavitt row and
column.  Equality of finite cardinalities forces this set to be zero, hence
`A=0` in the quotient.  Therefore the marked root belongs to the
representation kernel.
