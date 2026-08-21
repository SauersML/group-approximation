---
rg: 2
id: approximate-doubling-invariant-joint-measure-is-atomic
kind: claim
title: Coupled parabolic data is near one common finite odd-order operator model
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  parabolic-spectrum-is-doubling-invariant: that is the single-parabolic spectral constraint; this is the joint rigidity that would actually close the far sector, using the coupling the ambient group imposes.
---

OPEN.  Replace the vacuous scalar-measure target by an operator target.
Prove (or refute) that a sufficiently accurate finite-dimensional tuple for
`SL_2(Z[1/2])`, including the two fourth-power conjugacies, the
`S`-conjugation between opposite parabolics, and the half-parabolic edge
relations, is close in normalized HS to one common finite-dimensional model
in which the parabolics have a common finite odd order and all the coupling
words hold exactly.  The modulus must be independent of matrix dimension.

## Attempts

- The scalar Wasserstein version is invalidated by
  `odd-root-wasserstein-target-is-vacuous`: odd roots are dense, so every
  measure has such approximants.  The claim must control eigenvectors,
  multiplicities and joint moments strongly enough to reconstruct operators.
- **Noncommutative transfer route.**  Work with finite collections of mixed
  moments in `U,L,S` and the square-root word rather than marginal measures.
  The desired gap would have to exclude continuous invariant states while
  remaining compatible with congruence models converging to the regular
  trace.  No such joint-moment gap is presently proved.
- **Numerical status.**  `experiments/psl2_far_sector_probe.py` only measures
  distance from *short* tested odd orders.  It is a bounded falsifier for
  candidate optimization landscapes, not evidence for the operator theorem.
