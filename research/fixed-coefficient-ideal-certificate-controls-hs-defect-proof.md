---
rg: 2
id: fixed-coefficient-ideal-certificate-controls-hs-defect-proof
kind: route
title: Compress relator residuals and telescope the bounded certificate
target: fixed-coefficient-ideal-certificate-controls-hs-defect
requires:
  - regular-chart-wedderburn-coefficient-compiler
---

Let

```text
delta=max_j ||r_j(U)-1||_2.
```

Every compiled residual block has the form

```text
e R_j(U) f
```

with `e,f` fixed Fourier matrix units or projections.  Left and right
multiplication by these operators are contractions in normalized
Hilbert--Schmidt norm, so

```text
||R_j(U)||_2 <= delta.                                (CIP1)
```

A fixed star-polynomial in coefficient blocks of unitary inputs has a fixed
operator-norm bound: each coefficient block is a compression of a unitary and
has operator norm at most one, and the triangle inequality bounds a polynomial
by the sum of the absolute values of its finitely many scalar coefficients.
Write `M_q,N_q` for bounds on the two multipliers in one summand of `(CIC1)`.
The Schatten ideal inequality gives

```text
||A_q R_(j_q) B_q||_2
 <= ||A_q||_infty ||R_(j_q)||_2 ||B_q||_infty
 <= M_q N_q delta.                                   (CIP2)
```

The same estimate applies to adjoint residuals.  Summing the finitely many
terms in the certificate therefore gives

```text
||D(U)||_2
 <= (sum_q M_q N_q + sum_q M'_q N'_q) delta.         (CIP3)
```

The parenthesized constant depends only on the fixed certificate.  Neither the
number nor the norms of its terms depend on the external multiplicity `k`.
Finite matrix amplification merely repeats the same argument blockwise, with a
fixed additional finite sum.  This proves the claim.