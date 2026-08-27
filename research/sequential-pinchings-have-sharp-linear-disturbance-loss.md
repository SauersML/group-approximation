---
rg: 2
id: sequential-pinchings-have-sharp-linear-disturbance-loss
kind: claim
title: Sequential pinching has an unavoidable linear disturbance loss on sparse Clifford cycles
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that lower-bounds distance to every commuting tuple; this computes the canonical sequential-product POVM marginals for every measurement order.
  commutator-threshold-sets-need-not-be-stopping-sets: that is a one-face spectral-mixture obstruction; this gives an extensive disturbance-to-energy ratio for sequential global measurement.
  bounded-local-unitary-sum-verifier-no-go: that treats generic normalized-sum word verifiers; this is an exact projective-measurement/pinching calculation.
---

Let `Q_1,...,Q_L` be the sparse Clifford-cycle reflections from
`sparse-clifford-cycles-refute-average-commutator-rounding`: neighbors on the
cycle anticommute and all other pairs commute.  For a measurement order
`pi`, form the standard sequential-product POVM from the binary spectral
projections of the `Q_i`.  Its Heisenberg marginal reflection for coordinate
`pi(k)` is

```text
R_(pi(k))=Phi_(pi(1)) ... Phi_(pi(k-1))(Q_(pi(k))),
Phi_j(X)=(X+Q_j X Q_j)/2.                                  (SPL1)
```

If neither cycle neighbor of `i` occurs before `i`, then `R_i=Q_i`.  If at
least one neighbor occurs before it, that neighbor's pinching sends `Q_i` to
zero, and every later pinching preserves zero.  Hence

```text
||R_i-Q_i||_2^2 = 0 or 1                                  (SPL2)
```

according as `i` precedes both neighbors or not.

The vertices preceding both neighbors form an independent set in the cycle,
so there are at most `floor(L/2)` of them.  Therefore every deterministic
order satisfies

```text
(1/L)sum_i ||R_i-Q_i||_2^2 >= 1/2.                         (SPL3)
```

For a uniform random order, each vertex is earliest among itself and its two
neighbors with probability `1/3`, giving expected disturbance `2/3`.
Meanwhile the complete ordered-pair commutator energy is `8/L`.  Thus the
ratio between sequential marginal disturbance and pair energy is
`Omega(L)`, sharply realizing the usual accumulated-disturbance loss.

No subsequent POVM orthogonalization can turn this particular construction
into a global PVM close to the original `Q_i`: such a PVM has commuting
binary marginals, and the cycle tuple is already a constant average distance
from every commuting tuple.  Random ordering, palindromic sequential
effects, and orthogonalization therefore do not by themselves provide a
dimension-independent same-PVM theorem.

This does not refute a parity-aware LDPC correction: the sparse cycle fails
the parity faces.  It proves that the parity/fundamental-cone information
must be used **before or inside** the measurement construction to align
spectral mixtures; appending it after a generic sequential POVM cannot
repair the linear loss.
