---
rg: 2
id: approximate-doubling-invariant-joint-measure-is-atomic
kind: claim
title: An approximate representation whose two parabolics are doubling-invariant and involution-matched is near an atomic-spectrum one
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  parabolic-spectrum-is-doubling-invariant: that is the single-parabolic spectral constraint; this is the joint rigidity that would actually close the far sector, using the coupling the ambient group imposes.
---

Make precise and prove (or refute) the following.  There is a modulus
`f`, `f(0^+) = 0`, such that any finite-dimensional unitary tuple modelling
`SL_2(Z[1/2])` with relator defect `<= delta` (on a fixed finite set of
relators including `h U h^(-1) U^(-4)`, `h L h = L^(-4)` wait sign, the
`S`-conjugation `S U S^(-1) L`, and the half-parabolic relations) has its
parabolic spectral measure within `f(delta)` (Wasserstein) of a measure
supported on odd roots of unity.

## Attempts

- This is the analytic core of the far sector and is not yet proved.  The
  single-parabolic version is false (Gibbs measures), so the coupling is
  essential.
- **Transfer-operator route.**  For the doubling map `T_4(z) = z^4`, the
  Ruelle operator on the coupled data (parabolic + opposite via the
  involution) may have a spectral gap on the codimension-one subspace of
  signed measures orthogonal to the atomic invariant measures, once the
  half-parabolic constraint restricts to the arithmetic (odd-root)
  invariant measures.  The half-parabolic `U^(1/2)` exists in the rep, so
  the spectrum is also `z -> z^2`-invariant (from `diag(sqrt2,1/sqrt2)`,
  which is NOT in the group, but `U^(1/2)` conjugated by `h` gives a
  half-step): this doubles the constraint to `z -> z^2`-invariance, whose
  only finite invariant sets are again odd roots of unity but whose
  continuous invariant measures are still Lebesgue + Gibbs.
- **Numerical status.**  `experiments/psl2_far_sector_probe.py` searches for
  low-defect tuples with parabolic far from odd roots of unity; a clean
  tradeoff `defect >= g(farness)` supports this claim, a defect collapse at
  fixed farness refutes it and the stability of `SL_2(Z[1/2])`.
