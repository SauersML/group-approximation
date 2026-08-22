---
rg: 2
id: nonhyperlinear-via-canonical-tight-multiplicity-checksum
kind: route
title: Replace runtime-uniform Clifford explosion by a canonically tight dimension checksum
target: non-hyperlinear-group
requires:
  - depthwise-canonical-kleene-needs-no-uniform-runtime-gap
  - multiplicity-pi-turing-tape
  - boone-commutator-criterion-for-halting
  - canonical-tight-orthogonal-checksum-collapses-one-mark
  - canonical-tight-multiplicity-block-checksum
---

Use the exact finite-group isotypic carrier and its multiplicity commutant as
the matrix tape.  At each fixed detected size `k`, the finite
Amitsur--Levitzki instruction and Boone control provide `(CTM2)`; no
runtime-uniform constant is requested.  Canonical tightness `(CTM1)` and the
orthogonal checksum theorem collapse the same marked carrier after taking
the canonical microstate limit and then the depth limit.  The depthwise
reverse-Kleene theorem converts that collapse and Boone's exact nonhalting
mark into a finitely presented nonhyperlinear group.

This route is strictly weaker than
`same-model-supercritical-clifford-trigger` in constant-gap uniformity and
strictly stronger in trace structure: it replaces `d>=F(d)>d` by a tight
canonical decomposition of all finite multiplicity types.  Escaping mass at
`k_m->infinity` is the mandatory falsification test.
