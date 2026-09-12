---
rg: 2
id: rank-density-quadratic-selection-proof
kind: route
title: Cut at one half, recover moments by compactness, and remove nonextendible stage traces
target: rank-density-is-quadratic-trace-selection
requires: []
artifacts:
  - research/artifacts/ash-rank-quadratic-selection-2026-09-11.md
---

Sections 1--2 of the artifact give the complete proof.

The scalar inequality `|1_(1/2,1](t)-t|<=2t(1-t)` gives
`Delta<=3E`. In the reverse direction, if `d(a)` is within `delta` of the
continuous target, compactness makes one continuous cutoff `b=g_k(a)`
satisfy `f-delta-eta<tau(b^2)<=tau(b)<f+delta` at all traces, so
`E<=2delta+eta` and `E<=2Delta`.

At a fixed matrix size the moment objective is norm continuous. For a
fixed stage, the restrictions of later-stage trace spaces form a decreasing
family of compact sets whose intersection is precisely the restrictions
of limit traces. Thus an error bound on limit traces holds on every trace
of a sufficiently late stage. Subhomogeneous extreme traces are normalized
irreducible matrix traces. Conversely, Brown--Perera--Toms Proposition 5.1
approximates any continuous strictly positive affine target by a positive
stage-element evaluation, so the fibre selection property recovers rank
density. All normalizations and error bounds are explicit in the artifact.
