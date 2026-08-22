---
rg: 2
id: transitive-controller-zero-lcu-proof
kind: route
title: Factor the common equivariant holonomy out of the LCU sum
target: transitive-controller-orbit-common-twist-preserves-zero-lcu
requires:
  - finite-symmetry-equivariant-edge-has-one-holonomy
---

Use the common multiplicity unitary from the equivariant edge and distribute
the finite sum to obtain `(TCO2)`.  Unitary invariance of normalized
Hilbert--Schmidt norm gives `(TCO3)` by the triangle inequality.  Conjugating
one controller relation proves the payload-transport boundary `(TCO4)`.
For the cyclic hostile test, the edge covariance equation says precisely
that `pi(w_i)^*T_i` intertwines `pi` with itself, proving `(TCO5)`; compression
onto the constant clock vector gives `(TCO6)`.  Multiplying the edge blocks
around the cycle leaves only one product relation among the commutant
factors.
