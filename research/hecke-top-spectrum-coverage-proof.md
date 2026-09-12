---
rg: 2
id: hecke-top-spectrum-coverage-proof
kind: route
title: Turn near-top Hecke eigenvectors into a unital Kraus frame
target: hecke-top-spectrum-coverage-controls-window
requires:
  - regular-core-window-is-a-hecke-kraus-hull
---

The expectation \(E_D\) is the Hilbert--Schmidt orthogonal projection.
Hence equality in the contraction
\(A\mapsto E_D(X_0AX)\) occurs exactly when \(X_0AX\in D\), proving
(HTS2).  The Hecke--Kraus formula turns a unital frame of such equality
vectors into \(X\).  Conversely, a ucp map taking \(X_0\) to the unitary
\(X\) has \(X_0\) in its multiplicative domain, so every Stinespring
column is an equality vector.  Full right support can be normalized because
the sum of the right moduli is invertible and commutes with \(X\).

For the near-top statement, spectral calculus gives

\[
\sum_j\|X_0A_j-A_jX\|_2^2
 =2\sum_j\langle A_j,(1-T_X)A_j\rangle
 \leq2\epsilon\sum_j\|A_j\|_2^2=2\epsilon.
\]

Multiplication of the error column by the coisometric row
\((A_1^*,\ldots,A_q^*)\) produces
\(\sum_jA_j^*X_0A_j-X\), proving (HTS5).
