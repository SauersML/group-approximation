---
rg: 2
id: quantum-expander-relative-commutant-rounding
kind: claim
title: A quantum-expander check rounds uniformly to the old spin factor's commutant
distinct_from:
  finite-group-intertwiner-laplacian-gap: that averages a fixed finite group and its constant depends on that group; this uses a constant-degree quantum expander and remains uniform as the spin dimension grows.
  finite-group-shared-overlap-polar-alignment: that aligns two already exact finite-group actions; this first moves an arbitrary operator close to the commutant of a growing matrix factor.
---

Let `Phi:M_N->M_N` be a unital random-unitary channel

```text
Phi(Y)=(1/D) sum_(j=1)^D U_j Y U_j*,
```

whose Hilbert--Schmidt norm on traceless matrices is at most `lambda<1`.
For every `r` let

```text
E:M_N tensor M_r -> I_N tensor M_r
```

be the trace-preserving conditional expectation. Then every
`X in M_N tensor M_r` satisfies

```text
||X-E(X)||_2
 <= (1/(1-lambda))
    ((1/D) sum_j ||[X,U_j tensor I_r]||_2^2)^(1/2).              (QEC1)
```

All norms are normalized Hilbert--Schmidt norms. The constant is independent
of both `N` and the residual multiplicity `r`.
