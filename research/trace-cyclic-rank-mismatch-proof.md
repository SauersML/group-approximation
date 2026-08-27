---
rg: 2
id: trace-cyclic-rank-mismatch-proof
kind: route
title: Subtract the two cyclic traces and apply normalized Cauchy--Schwarz
target: trace-cyclic-rank-mismatch-checksum
requires: []
---

Finite-dimensional cyclicity gives `tr_d(YX)=tr_d(XY)`.  Insert this common
scalar between `tr_d(E)` and `tr_d(F)` and apply the triangle inequality to
obtain `(TCM2)` from `(TCM1)`.  The normalized trace functional has norm one
for normalized Hilbert--Schmidt norm, so `(TCM3)` implies `(TCM1)`.  If
`F=E-P`, then `tr_d(E)-tr_d(F)=tr_d(P)`, proving `(TCM4)`.

For amplification, both normalized trace and normalized HS norm factor over
`I_k`.  On `End(M_d tensor C^k)`, a Reynolds range of the form
`range(R) tensor End(C^k)` has rank `k^2 rank(R)` inside dimension
`k^2d^2`, proving the adjoint assertion.
