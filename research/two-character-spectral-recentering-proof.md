---
rg: 2
id: two-character-spectral-recentering-proof
kind: route
title: Compare the old cut sign with one separating reflection
target: two-code-character-cut-recenters-to-one-coordinate
requires:
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - adjoint-parity-cone-lifts-to-loewner-order
---

Fix `k` with `chi_k!=psi_k`.  Equation `(TCR1)` gives

```text
R_k=chi_k(p-q),          p=(I+chi_k R_k)/2.
```

The contraction/sign ledger, for this one cut, gives

```text
||R_k-X_k||_2^2<=||I-X_k^2||_2^2<=||[p,Q_k]||_2^2.
```

The diagonal and off-diagonal parts of `Q_k-R_k` are Hilbert--Schmidt
orthogonal.  Hence

```text
||Q_k-R_k||_2^2
 =||Q_k-X_k||_2^2+||X_k-R_k||_2^2
 <=2||[p,Q_k]||_2^2.
```

Since `p_k=(I+chi_kQ_k)/2`, this proves `(TCR3)`.  Directly from `(TCR2)`,

```text
[p_k,Q_i]=(chi_k/2)[Q_k,Q_i],
```

which proves `(TCR4)`.  Finally `(APL7)` bounds every complete-pair row by
`E_com/kappa`, giving `(TCR5)`.
