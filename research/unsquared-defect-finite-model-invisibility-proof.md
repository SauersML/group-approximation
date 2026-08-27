---
rg: 2
id: unsquared-defect-finite-model-invisibility-proof
kind: route
title: Finite commutant-dimension proof of defect invisibility
target: unsquared-defect-finite-model-invisible
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralFiniteDimensionalObstruction.lean
---

## Direct proof

Let `C` be the commutant of the image of the literal property-(T) base in a
finite-dimensional representation and let conjugation by the image of `t` be
`Phi`.  The one-sided compression relation gives `C <= Phi(C)`.  Since `Phi`
is a linear isomorphism and `C` is finite-dimensional, equality holds.  The
image of `c` lies in `C`, hence so does the image of `t c t^-1`; it therefore
commutes with the image of `v_1`, killing `u`.  A finite group embeds in a
finite-dimensional permutation representation, giving the final assertion.
