---
rg: 2
id: sofic-non-mf-witness-proof
kind: route
title: Build the sofic telescope and transport the invisible sign to it
target: sofic-non-mf-witness
requires: [literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralWitnessConsequences.lean
  - GroupApproximation/Sofic/SoficTelescope.lean
  - GroupApproximation/Sofic/SoficInvariantFiniteKernel.lean
  - GroupApproximation/Sofic/SoficIntegerExtension.lean
---

## Why sufficient

Finite Clifford stages over the finite coset sets have a finite-index copy
of the residually finite affine base and are sofic.  Their directed union is
sofic; the automorphic direct limit of the injective dilation is sofic; and
the final split integer extension is sofic.  The stabilizer computation
identifies this telescope with `W`.  The literal map `E -> W` is surjective,
sends `w` to the nontrivial Clifford sign, and its six Tietze generators
generate `W`.  Corona-kernel portability therefore makes `W` non-MF.
