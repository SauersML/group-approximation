---
rg: 2
id: right-regular-multiflip-hole-charge-proof
kind: route
title: Diagonalize a right-regular flip against the complete-graph transfer
target: right-regular-multiflips-have-exact-cubic-hole-charge
requires:
  - prime-iwahori-endpoint-transfer-is-complete-graph-hecke
  - near-top-hecke-coverage-has-exact-hole-dual
  - almost-full-hecke-frame-gives-flexible-corner
---

Every element of the right group algebra commutes with the canonical left
regular tuple. Thus \(C=C^*=C^{-1}\), \(X^2=1\), and the inversion relation
is unchanged. Each canonical cubic contains three copies of \(X_0\);
replacing them by \(CX_0\) inserts \(C^3=C\), proving (MFC2)--(MFC3).

Right \(D\)-bimodularity gives \(T_X=R_CT_0\). The endpoint transfer is
right modular over the whole right group algebra, so \(R_C\) and \(T_0\)
commute. On the \(1\)-eigenspace
\(\mathbb C[G]^{\rm op}\) of \(T_0\), right multiplication by \(C\) has
positive eigenspace \(\mathbb C[G]^{\rm op}(1-P)\). On the orthogonal
complement, every eigenvalue of \(T_0\) is \(-1/p\); after multiplication
by the involution \(R_C\), the only possible eigenvalues are
\(\pm1/p\). Under (MFC5) none enters the near-top interval. This proves
(MFC6).

If \(A\in\mathbb C[G]^{\rm op}(1-P)\), then \(AP=0\), so
\(A^*AP=0\). Every contractive sum of such squares is supported on
\(1-P\) and has trace at most \(1-\tau(P)\). The single column \(1-P\)
attains that value. This proves (MFC7)--(MFC8), and the almost-full-frame
estimate gives (MFC9).
