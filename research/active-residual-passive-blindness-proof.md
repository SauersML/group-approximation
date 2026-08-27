---
rg: 2
id: active-residual-passive-blindness-proof
kind: route
title: Adjoin one common compressed Weil cell to two cuspidally redistributed endpoints
target: active-residuals-do-not-name-passive-endpoint
requires:
  - cuspidal-redistribution-refutes-regular-core-orbit-basin
  - even-weil-fixed-line-compression
  - positive-fixed-corner-cubic-energy-charges-deleted-rank
---

Choose once and for all a determinant-neutral even-Weil endpoint `tau` and
compress one of its neutral parabolic fixed lines.  Denote the resulting
near tuple by

```text
C=(X_C,R_C,S_C)
```

and its nonzero cubic residuals by `D_1,D_2`.  Restoring the deleted line
recovers `tau`; the positive-corner identity charges its rank by
`||D_1||_F^2`.

For the primes in
`cuspidal-redistribution-refutes-regular-core-orbit-basin`, align the exact
representations `rho_p,eta_p` so that

```text
rho_p|B=eta_p|B=beta_p.                                  (APR1)
```

Choose integers `k_p->infinity` with
`k_p dim(C)=o(dim rho_p)` and form

```text
T_p =C^(+k_p) (+) rho_p,
T_p'=C^(+k_p) (+) eta_p.                                (APR2)
```

Their BS cores are both `(R_C,S_C)^(+k_p) (+) beta_p`.  Since the passive
summands are exact representations of `A`, direct evaluation of the two
cubic words gives in both cases

```text
D_i^(+k_p) (+) 0,                 i=1,2.                (APR3)
```

This proves all of the operator-valued residual-data assertions, not merely
equality of traces or singular spectra.  The common active block has rank
tending to infinity but normalized dimension `o(1)`.  The positive-corner
lower bound and the fixed-word upper bound make its unnormalized cubic
energy `Theta(k_p)`, so its full rank is genuinely energy-paid rather than
being a bounded decoration.

Suppose `(ARP4)` failed.  Compress any core-commutant conjugating unitary to
the passive summands.  The `o(d_p)` active summand changes the normalized
Hilbert--Schmidt norm by `o(1)`.  Polarizing the passive compression, or
equivalently using the standard two-projection block estimate, produces a
unitary in `beta_p(B)'` with

```text
||eta_p(x)-U rho_p(x)U^*||_2=o(1),                      (APR4)
```

contradicting `(CRB4)`.  Hence the macroscopic passive separation survives
adjoining the common active cell.

Finally, adding back the same `k_p` deleted lines to `(APR2)` gives the exact
endpoints `tau^(+k_p) (+) rho_p` and `tau^(+k_p) (+) eta_p`.  Therefore the example is a
blindness theorem for global type selection, not a counterexample to local
boundary completion or to flexible stability.
