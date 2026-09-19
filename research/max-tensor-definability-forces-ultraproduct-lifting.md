---
rg: 2
id: max-tensor-definability-forces-ultraproduct-lifting
kind: claim
title: Uniform maximal-tensor definability forces max-ultraproduct liftability and fails globally
distinct_from:
  llp-implies-weak-ucp-stability: That turns LLP of one full group C-star algebra into weak ucp stability; this is a model-theoretic obstruction to uniformly defining the maximal tensor norm and does not establish LLP or its failure for a candidate group.
  leavitt-llp-permanence-fence: That audits group-theoretic LLP permanence at the binary Leavitt group; this gives a general ultraproduct-definability fence and no Leavitt-specific conclusion.
  exact-local-reflexivity-does-not-promote-hyperlinear-traces: That separates exactness/local reflexivity from MF trace promotion; this separates first-order maximal-tensor definability from arbitrary C-star algebras through the max-ultraproduct map.
artifacts:
  - research/artifacts/goldbring-sinclair-tensor-definability-audit-2026-08-23.md
---

**ESTABLISHED (Goldbring--Sinclair, arXiv:2509.15086v1).**  For a C-star
algebra `A` and ultrafilter `U`, let property `max-U` mean that the canonical
map

```text
A^U tensor_max A^U  ->  (A tensor_max A)^U
```

is isometric.  If the maximal tensor norm is definable over a theory `T`,
then every model of `T` has property `max-U` for every ultrafilter `U`.
There are C-star algebras without property `max-U`; in particular the
maximal tensor norm is not uniformly definable across all C-star algebras.

The negative examples use Pisier's ultraproduct characterization of the
lifting property: starting from a group full C-star algebra without LP,
Goldbring--Sinclair construct a separable algebra that fails property
`max-U` for every relevant cofinal ultrafilter.  Hence a proposed universal
maximal-tensor formula cannot serve as a generic ultraproduct-to-coordinate
lifting or trace-promotion device.

This is only a fence.  Failure of definability does not imply failure of LLP
for any particular group, and it does not produce a non-hyperlinear group.
