---
rg: 2
id: leavitt-df-failure-from-half-corner-comparison
kind: route
title: Install the chart comparison with the half-corner upper and lower shears and pad by the complement
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - half-corner-chart-comparison-exists
artifacts:
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
---

## Why sufficient

Given `Z, L` with `L Z = f_+` and `Z in P S f_+`, conjugate the source by `U`:
`Z U` and `U^-1 L` compare `f = U^-1 f_+ U` with `P`. Half-corner Section 5 then
supplies the controlled upper shear `M = M_0 + P(a f + Z U) j` with `a_M f = Z U`,
and the lower shear `K = c f U^-1 L`. These satisfy the two half-equations `(H)`
of Section 2. Section 2 gives `C a_M = e` with `C = (e + R) B`, and `a_M C != e`
because evaluation sends `a_M` to `a_0`, which `p_01` annihilates on the left.
Padding `a_M` and `C` by `q = 1 + e` gives `alpha beta = 1 != beta alpha` in `S`.

## Not a restatement

The prerequisite is a module comparison between two fixed finite-chart
projectives with no evaluation condition. The target is the existence of an
arbitrary strict one-sided inverse pair. The route supplies all of the shear
algebra, the Drazin split `f = e + T^2` and the strictness argument, none of
which the prerequisite mentions. A direct finiteness failure need not arise
through this chart or this pair of projectives.
