---
rg: 2
id: rank-one-regular-flip-davis-kahan-proof
kind: route
title: Flip the constant right-regular line and trace the transfer exactly
target: rank-one-regular-flip-refutes-relator-davis-kahan
requires:
  - prime-iwahori-endpoint-transfer-is-complete-graph-hecke
  - almost-full-hecke-frame-gives-flexible-corner
---

The constant projection is the average of the right regular
representation, so it lies in \(\lambda(G)'\) and commutes with the
canonical tuple. Hence \(C^2=1\), \(X^2=1\), and every word containing
two copies of \(X\), including the inversion row, is unchanged. Each
canonical cubic contains three copies of \(X_0\); replacing them by
\(CX_0\) inserts \(C^3=C\), proving (RDK2)--(RDK4).

For \(A\in D\),

\[
T_X(A)
 =E_D(X_0ACX_0)
 =E_D(X_0AX_0C)
 =T_0(A)C,
\]

using commutation of \(C\) with \(X_0\) and right \(D\)-bimodularity of
the expectation. Since \(P\) is in the canonical top right-regular algebra,
(RDK6) follows. After normalizing \(P\) in \(L^2(D)\), the transfer
difference has norm two; two contractions can differ by at most two, so
(RDK7) is exact. The complete-graph endpoint formula shows that every
regular-orbit endpoint transfer has spectrum \(\{1,-1/p\}\). Spectral
Hausdorff distance for selfadjoint operators, applied to the eigenvalue
\(-1\) of \(T_X\), proves (RDK8). The vector \(P\) also witnesses
norm-one movement of the canonical sharp spectral projection.

Finally, \(T_0(1-P)=1-P\) and \((1-P)C=1-P\), so \(1-P\) is an exact top
vector for \(T_X\). Its square is the contractive carrier \(1-P\), whose
missing normalized trace is \(1/|G|\). Apply the almost-full-frame estimate
with \(\epsilon=0\) and \(\delta=1/|G|\).
