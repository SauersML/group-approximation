---
rg: 2
id: kernel-resolutions-uniform-cost-proof
kind: route
title: Bound each supported marginal by its range projector and count local energy occurrences
target: kernel-resolutions-and-local-spectra-bound-rounder-cost
requires: [finite-syndrome-cost-is-a-kernel-support-cone-test, bounded-overlap-syndrome-energy-accounting, fixed-term-chain-defeats-bounded-syndrome-neighborhoods]
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
---

Theorem 3 of the kernel-resolution artifact proves the positive bound and
finite-collection corollary. Every marginal is a
positive contraction supported on `ran A_a`, hence is bounded by its range
projector and then by `A_a/delta`. Bounded occurrence gives cost
`R/delta`, while the same feasible effects give exact recovery. For the
finite term collection corollary, finitely many local matrices and local
incidence patterns give finitely many neighborhood spectra. The minimum
positive eigenvalue over that finite collection is positive; zero matrices
have zero required marginals.

For the explicit insufficiency clause, the fixed-term chain prerequisite
supplies a bounded-degree qubit family with the stated uniform local
spectral bound but no finite-cost local syndrome instrument for the
displayed range of `n,L,R`. The finite-cost characterization therefore
excludes its kernel resolutions. Its vanishing combinatorial gap explains
why this does not refute a construction for the special amplified family.
