---
rg: 2
id: maximally-entangled-vectorization-is-hs-isometry
kind: claim
title: Transpose action on a maximally entangled vector is normalized-HS isometric
distinct_from:
  consistency-defect-is-state-dependent-distance: that identifies a projection consistency expression in an arbitrary tracial state; this is the exact finite-matrix vectorization identity for arbitrary matrices and the canonical maximally entangled state.
---

Let

```text
Phi_d=d^(-1/2) sum_(j=1)^d e_j tensor e_j.
```

For all `A,B in M_d(C)`, with normalized Hilbert--Schmidt norm,

```text
||(A tensor conjugate(B))Phi_d-Phi_d||^2
  = ||A B^*-I||_2^2.                                           (MEH1)
```

In particular, for unitaries `A,B`,

```text
||(A tensor conjugate(B))Phi_d-Phi_d||
  = ||A-B||_2.                                                  (MEH2)
```

Thus copying a finite-dimensional unitary word oracle to the second player by
entrywise conjugation converts normalized-HS word consistency errors into
state-dependent errors with no loss and no dependence on `d`.

