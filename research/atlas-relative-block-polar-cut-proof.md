---
rg: 2
id: atlas-relative-block-polar-cut-proof
kind: route
title: Threshold the largest admissible relative-unitary block
target: atlas-relative-block-polar-cut-reduction
requires:
  - unitary-block-energy-transport
  - atlas-full-relator-data-factor-through-double-commutant-gauge
  - atlas-a8-mixed-block-transport-has-permutation-models
  - positive-cross-gram-mass-alone-has-no-holonomy-floor
---

Pigeonhole `(RBP1)` to a block `T=P_iUQ_j` of squared Hilbert--Schmidt mass
at least `alpha/|E|`.  Threshold `T^*T` at
`lambda=alpha/(2|E|)`.  Since `0<=T^*T<=1`, splitting its trace below and
above the threshold gives `(RBP2)`.  Its polar decomposition on the spectral
cut gives equal source and target ranks, the singular floor `(RBP3)`, and the
inverse bound `(RBP4)`.

The double-commutant transformation law makes the maximizing label and its
mass invariant and makes the spectral cut and polar map equivariant.  Hence
this is a legal mixed finite-coordinate selection, unlike a selector formed
from the two packet tables separately.

Taking `E` to be the full block menu and applying the exact transportation
identity proves `(RBP5)` and the unconditional untyped cut.  For a proper
typed menu, the permutation absorber shows that regular margins alone give
no stronger localization whenever the complementary support carries a
transport plan.  Finally the fixed-overlap holonomy no-go rules out replacing
one simultaneous typed incidence by several independently selected positive
corners.  This proves both the construction and its exact limitation.
