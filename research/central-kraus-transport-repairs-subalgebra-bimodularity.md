---
rg: 2
id: central-kraus-transport-repairs-subalgebra-bimodularity
kind: route
title: Project Kraus operators to the commutant and balance both marginal deficits block by block
target: averaged-subalgebra-energy-repairs-bistochastic-channels
requires: []
artifacts:
  - research/artifacts/subalgebra-energy-and-bistochastic-kraus-repair-2026-09-08.md
---

Haar averaging the commutator energies over `U(B)` identifies
`a_B(P)` with the sum of squared distances of the Kraus operators
from `B'`. Project the Kraus operators onto that commutant. The
two positive marginal deficits need not be equal as operators,
but have equal trace on every simple central summand of `B'`.
An explicit rank-one transport on each summand supplies Kraus
operators with precisely those two marginals.

The resulting channel is unital, trace-preserving and `B`-bimodular.
Its Stinespring column is at squared normalized-HS distance
`2a_B(P)` from the original one, proving the displayed estimate.
Apply the same argument to adjoint Kraus operators before averaging
the repaired channel with its Hilbert-space adjoint. This gives
self-adjointness without assuming that taking adjoints preserves
the infinity-to-two norm.

For the final expectation estimate, exact bimodularity and trace
preservation give `E_B Q=E_B`. Its outputs can therefore be
compared to `B` using the orthogonal projection `I-E_B`. The
two-dimensional sharpness example is an exact conditional expectation
onto a slightly rotated diagonal algebra.
