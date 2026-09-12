---
rg: 2
id: spectral-coarea-and-corner-reflection-prove-quantum-cheeger
kind: route
title: Reflect the lost corner mass and integrate the small-projection expansion inequalities
target: reflected-corners-control-defective-quantum-variance
requires: []
artifacts:
  - research/artifacts/reflected-corner-quantum-cheeger-bound-2026-09-08.md
---

For `H=p-pK(p)p`, the map
`K_ref(a)=pK(a)p+H^(1/2)aH^(1/2)` is self-adjoint and bistochastic
on `pM_dp`. It lowers the Dirichlet energy of self-adjoint matrices.
For projections it loses at most `tr(H)=E_K(p)`, so the original
expansion bound transfers with additive defect `kappa+E_K(p)`.

Choose a spectral median inside `p` and split the centered matrix
into its positive and negative parts. Both supports have trace at
most half the corner trace. Positivity and self-adjointness make
the channel weights between their spectral projections nonnegative
and symmetric. Spectral coarea and Cauchy--Schwarz then bound each
integrated projection boundary by the square root of twice its
energy times its squared Hilbert--Schmidt norm. Summing the two
parts and using Young's inequality gives the stated constants.

The unreflected energy seminorm gives the second estimate directly.
An expectation onto two equal block-scalar algebras in `M_4` supplies
the example with zero energy and positive corner variance; all small
quantum subprojections are checked, not just diagonal ones.
