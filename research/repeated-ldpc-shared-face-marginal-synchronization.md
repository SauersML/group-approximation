---
rg: 2
id: repeated-ldpc-shared-face-marginal-synchronization
kind: claim
title: Synchronize repeated LDPC face PVMs to literal shared marginals without losing the local code structure
distinct_from:
  constant-size-private-basins-give-uniform-root-control: that transfers one selected root to one anchor through a fixed basin; this must synchronize every parity-face occurrence while retaining its joint PVM.
  binary-face-pvm-is-determined-by-coordinate-reflections: that gives uniqueness once marginals are literally equal; this must obtain literal equality from average occurrence defects.
---

OPEN.  From small average fixed-face PVM defect and bounded-degree equality-
expander defect in the repeated LDPC occurrence system, produce exact local
codeword PVMs on the same Hilbert space whose copies of each logical binary
coordinate are literally one shared reflection, with total squared movement
bounded by a dimension- and length-independent modulus.

Correcting each bounded face separately is uniform, and synchronizing bare
reflections on an equality expander is uniform in average.  Doing both at
once is not formal: replacing a face marginal by the synchronized reflection
can destroy joint commutation and parity, while re-correcting the face can
move its marginal again.  This is the finite-overlap agreement step needed
before the adjoint face-Hamiltonian gap can be applied.

`shared-face-synchronization-is-uniform-lcs-hs-stability` identifies this
step exactly with uniform same-dimension HS stability of the growing
homogeneous LCS colimits in their redundant occurrence presentations.  In
particular, the Lipschitz face-atom formula cannot be applied to independently
averaged spectral signs until their within-face commutation is already known.
