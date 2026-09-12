---
rg: 2
id: fpbs-pulled-back-graphing-isoperimetry-proof
kind: route
title: Average finite-set kernels and repair their row and column balance
target: fpbs-pulled-back-graphing-isoperimetry
requires: []
artifacts:
  - research/artifacts/fpbs/docs/isoperimetric-test-descent.md
---

Sections 2--5 contain the proof. Project n disjoint source
full-group graphs, truncate their group displacements to a finite
set D, and condition on the base. The resulting finite-set kernel
has expected incoming degree at most n. Average m independent
samples of this kernel; their excess incoming degree has integral
at most |D| sqrt(m) in expectation. Move the sampled sets by
powers of an aperiodic full-group map to remove overlaps up to
arbitrarily small measure, without changing their incoming degrees
or integrated boundaries.

Cap incoming degrees at mn. Grebik's approximate Konig theorem
then decomposes almost all remaining pairs into mn partial pmp
bijections. Extend them within the ergodic base relation, avoiding
previously assigned images. Boundary changes cost at most the
fixed degree bound times the number of altered vertices. Equation
(9) tends to the source boundary ratio. The reverse comparison
follows by lifting base full-group maps.

Imported: Grebik, Theorem 1.2(I), for approximate edge coloring;
standard existence of an ergodic full-group automorphism in an
ergodic type II_1 relation; and Pichot--Vassout for the optimized
cost identity in Section 6. The exact primary sources and the
finite-degree/ergodicity scope are given in the artifact.
