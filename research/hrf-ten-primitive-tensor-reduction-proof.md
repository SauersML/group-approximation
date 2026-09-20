---
rg: 2
id: hrf-ten-primitive-tensor-reduction-proof
kind: route
title: Apply the degree-nine obstruction and remove coprime factor cocycles by determinants
target: hrf-ten-detectors-are-primitive-and-not-two-by-five
requires:
  - hrf-mixed-nine-dimensional-maps-kill-five-mark
  - hrf-mixed-detectors-have-balanced-edge-spectra
  - hrf-amplified-sym4-five-twists-have-no-detectors
artifacts:
  - research/artifacts/hrf-ten-mixed-placement-2026-09-20.md
  - research/artifacts/hrf-mixed-spectral-balance-2026-09-20.md
---

A proper nonzero invariant subspace has degree at most nine and retains
the nontrivial scalar mark, contradicting the first premise. An action
on at most ten imprimitivity blocks kills every order-nineteen root
subgroup in each vertex. The two root subgroups generate PSL_2(F_19),
so each block is invariant under every vertex and the scalar mark,
contradicting irreducibility.

For a preserved 2 tensor 5 structure, each vertex has projective factor
representations a_g,b_g with opposite scalar cocycles c,c^-1.
The cochain t(g)=det(a_g)^3 det(b_g) has coboundary c, so rescaling
by t^-1,t yields genuine factor representations. In characteristic
nineteen PSL_2(F_19) has no nontrivial two-dimensional representation:
its simple dimensions are 1,3,5,...,19, and perfectness eliminates an
extension of trivial factors. The defining-characteristic classification
used here is cited and checked in the spectral-balance artifact.

Every vertex restriction is therefore two copies of a degree-five
module. The balanced edge spectrum forces that module to be L4,
as its only possible balanced composition vector in degree five.
Thus all vertices are of type 2L4, excluded by the last premise.
The separate artifact gives the full argument and gauge-correct system.
