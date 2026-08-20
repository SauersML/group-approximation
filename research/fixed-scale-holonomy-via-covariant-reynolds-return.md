---
rg: 2
id: fixed-scale-holonomy-via-covariant-reynolds-return
kind: route
title: Return the explicit adjoint Reynolds defect through a compressor-covariant coefficient
target: fixed-scale-contextual-multiplicity-holonomy
requires:
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - schur-complement-controls-relative-pauli-module
  - packet-kazhdan-commutant-placement-decouples
  - compressor-covariant-packet-reynolds-return
  - scaled-kazhdan-transport
  - bounded-overlap-syndrome-energy-accounting
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

The predicate lemma converts forbidden Hilbert mass `q` into an adjoint
projection defect of density at least `c_f q^2`.  The covariant-return gadget
places that very range in the scaled asymptotic commutant transported by the
one-sided compressor, and `(CPR1)` bounds its returned density by a
dimension-free relator-energy sum.  Bounded overlap converts that sum to the
global energy.  The tensor-decoupling theorem is included as a mandatory
falsification gate: the covariance relation, not bare commutant placement,
must do the work.
