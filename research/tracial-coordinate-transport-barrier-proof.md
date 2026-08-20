---
rg: 2
id: tracial-coordinate-transport-barrier-proof
kind: route
title: Standard-form failure, corner cost, and the explicit radical gap
target: tracial-coordinate-transport-barrier
requires:
  - mf-hyperlinear-radical-divergence
  - corner-renormalization-cost
artifacts:
  - docs/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
---

## Why sufficient

For an infinite finite factor `M` in standard form, `JMJ=M'` and
`M or M'=B(L^2 M)`, so the Murray--von Neumann comparison step used by
one-sided transport no longer occurs in a finite algebra.  The manuscript's
constant coordinates `A_n=C*_r(E)` turn this structural observation into an
explicit countermodel: the left regular representation is exact, `c`
centralizes the Kazhdan base, yet the transported commutator is nontrivial.

Independently, `corner-renormalization-cost` shows that a corner of relative
trace `delta` multiplies normalized 2-norms by the scale `delta^(-1/2)`, and
the architecture supplies no positive lower bound on that density in a
tracial model.

Finally `mf-hyperlinear-radical-divergence` gives a direct impossibility
certificate for the full tracial conclusion: the literal mark is killed by
every operator-norm corona homomorphism but detected by a hyperlinear model.
Thus no theorem saying every tracial model kills that mark can hold.
