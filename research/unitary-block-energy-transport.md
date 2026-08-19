---
rg: 2
id: unitary-block-energy-transport
kind: claim
title: Squared Fourier-block energies of a unitary form an exact transportation plan
---

Let `P_i` and `Q_j` be finite orthogonal decompositions of the identity in
`M_D(C)` and let `U` be unitary.  Put

```text
alpha_i = tr_D(P_i),
beta_j  = tr_D(Q_j),
m_(j,i) = ||Q_j U P_i||_2^2.                          (UBE1)
```

Then `m` is a nonnegative transportation plan from `alpha` to `beta`:

```text
sum_j m_(j,i) = alpha_i,
sum_i m_(j,i) = beta_j.                               (UBE2)
```

Consequently, for any real edge costs `c_(j,i)` and any real dual potentials
`x_i,y_j` satisfying

```text
x_i + y_j <= c_(j,i)                                  (UBE3)
```

for every pair `(i,j)`, one has the exact lower bound

```text
sum_(i,j) c_(j,i) ||Q_j U P_i||_2^2
 >= sum_i alpha_i x_i + sum_j beta_j y_j.             (UBE4)
```

Thus a positive rational dual value is a dimension-independent certificate
that every unitary must pay positive weighted block energy.  The weighted Hall
leakage bound is the zero-one cost special case: cost one on forbidden edges
and zero on allowed edges.

For regular finite-group charts, choosing minimal Wedderburn projections makes
`alpha_i,beta_j` fixed rational Plancherel weights independent of external
multiplicity.  This converts a finite Fourier obstruction into a transportation
LP rather than requiring a hard support graph.
