---
rg: 2
id: regular-core-hecke-kraus-hull-proof
kind: route
title: Decompose the induced regular core and take the commutant numerical radius
target: regular-core-window-is-a-hecke-kraus-hull
requires:
  - every-relative-ucp-window-lives-in-one-induced-representation
---

Write \(q=[G:B]\).  Restriction of the left regular representation gives
\(\lambda_G|_B\cong q\lambda_B\), so induction gives

\[
\operatorname{Ind}_B^G(\lambda_G|_B)\cong q\lambda_G.
\]

By the universal induced-host theorem, a relative ucp window is the
compression of this representation by a \(B\)-intertwining isometry.
Under the displayed decomposition such an isometry is a column
\(V=(A_1,\ldots,A_q)^T\), where every \(A_j\) belongs to
\(D=(\lambda_G(B))'\) and \(\sum_jA_j^*A_j=1\).  Compressing the marked
operator \(X_0=\lambda_G(x)\) gives exactly

\[
V^*(X_0\oplus\cdots\oplus X_0)V=\sum_jA_j^*X_0A_j,
\]

proving the Hecke--Kraus formula and the orbit upper bound.

For the numerical lower bound, let
\(T_Y(A)=E_D(X_0AY)\).  If \(X_0,Y\) are selfadjoint, trace cyclicity and
\(D\)-bimodularity of \(E_D\) give

\[
\langle C,T_YA\rangle
 =\tau(YC^*X_0A)
 =\langle T_YC,A\rangle.
\]

Thus \(T_Y\) is selfadjoint.  For every Kraus column,

\[
\tau\!\left(Y\sum_jA_j^*X_0A_j\right)
 =\sum_j\langle A_j,T_YA_j\rangle
 \leq\lambda_{\max}(T_Y)\sum_j\|A_j\|_2^2
 =\lambda_{\max}(T_Y).
\]

Duality of the Hilbert--Schmidt norm now gives (HKH9).  All spaces are
finite-dimensional, so no closure or attainment issue remains.
