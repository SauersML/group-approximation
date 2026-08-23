---
rg: 2
id: bs14-source-mode-reset-has-exact-frequency-cost
kind: claim
title: Resetting a scalar BS source mode costs exactly its cyclic frequency
distinct_from:
  bs14-long-packet-monodromy-reset-creates-fixed-sources: that chooses the principal return root and obtains a pi-over-m upper bound; this classifies every possible R-eigenmode reset and proves that one simple packet can supply at most one fixed source.
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that makes R-fixedness necessary for a neutral boundary; this computes the exact core movement needed to make a selected cyclic mode satisfy that condition.
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks the relator energy to pay the sum of inverse cyclic frequencies; this identifies the finite-packet source-selection operation whose cost that weighted estimate measures.
---

Let `(R,S)` be a multiplicity-one exact BS packet on one fourth-power orbit
of length `m`.  In the standard cyclic basis, `S` is diagonal and `R` is a
weighted cyclic shift with return phase `v`.  Its eigenvalues are the `m`
roots

```text
lambda_j=exp(i(theta+2 pi j)/m),       v=exp(i theta),
j in Z/m.                                                  (SMR1)
```

For every chosen mode `j`, put

```text
R_j=lambda_j^(-1)R.                                      (SMR2)
```

Then `(R_j,S)` is again an exact BS core, the `lambda_j`-eigenvector of `R`
is fixed by `R_j`, and

```text
||R-R_j||_(2,m)=|1-lambda_j|.                           (SMR3)
```

Conversely every exact covariance implementer on this same simple
`S`-orbit has fixed-space dimension at most one.  Thus a single scalar
packet can furnish at most one neutral boundary source after any
same-dimensional exact-core reset.  Producing two independent source modes
requires multiplicity or an additional copy of the length-`m` packet; it
cannot be obtained by taking the invariant hull of two selected vectors.

The source reset is cheap exactly for low cyclic frequency.  Choosing the
branch of `(SMR1)` nearest one recovers

```text
min_j ||R-R_j||_(2,m) <= 2 sin(pi/(2m)) <= pi/m,         (SMR4)
```

while a mode a fixed fraction around the cycle costs a fixed amount.  Hence
an active polar-data construction must either pay high-frequency modes by
energy or prove an aggregate weighted-frequency estimate after optimizing
the exact core.  A blanket `pi/m` reset for every selected source mode is
false.

## Scope

This is an exact reconnection operation and a capacity bound, not a proof
that the two cubic residual carriers canonically select the same modes.
That authentication and its energy budget remain the open content of
`bs14-residual-polar-data-build-active-dilation`.
