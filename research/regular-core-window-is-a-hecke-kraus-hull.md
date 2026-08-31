---
rg: 2
id: regular-core-window-is-a-hecke-kraus-hull
kind: claim
title: The regular-core relative window is a finite Hecke--Kraus hull
requires:
  - every-relative-ucp-window-lives-in-one-induced-representation
distinct_from:
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that controls the unitary commutant orbit of one exact regular endpoint; this identifies the larger matrix-convex set of all core-exact ucp corners before endpoint rounding.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies unitary exact endpoint orbits; this gives the finite Kraus parametrization of nonmultiplicative relative windows.
  right-core-cayley-average-gives-toeplitz-window: that constructs one unitary-fibre subfamily; this diagonalizes every relative ucp window on the regular finite core.
---

Let \(G\) be finite, \(B<G\), \(q=[G:B]\), and let
\(\lambda=\lambda_G\) on \(H=\ell^2(G)\).  Put

\[
\beta=\lambda|_B,\qquad D=\beta(B)'\subseteq B(H),\qquad
X_0=\lambda(x)
\]

for a marked involution \(x\in G\).  The set of all possible
\(x\)-coefficients of ucp maps

\[
\Theta:C^*(G)\longrightarrow B(H),\qquad
\Theta(u_b)=\beta(b)\quad(b\in B),                      \tag{HKH1}
\]

is exactly

\[
{\cal K}_{G,B}(X_0)=
 \left\{\sum_{j=1}^{q}A_j^*X_0A_j:
 A_j\in D,\ \sum_{j=1}^{q}A_j^*A_j=1\right\}.           \tag{HKH2}
\]

Thus the regular relative matrix range is the finite \(D\)-Kraus, or
\(C^*\)-convex, hull of the canonical endpoint \(X_0\).

Indeed, as a \(B\)-representation,

\[
\lambda_G|_B\cong q\lambda_B.
\]

Consequently

\[
\operatorname{Ind}_B^G(\beta)
 \cong q\,\operatorname{Ind}_B^G(\lambda_B)
 \cong q\lambda_G.                                     \tag{HKH3}
\]

By 'every-relative-ucp-window-lives-in-one-induced-representation', every
map in (HKH1) is a compression of (HKH3) by a \(B\)-intertwining isometry
\(V:H\to H^{\oplus q}\).  Write \(V=(A_1,\ldots,A_q)^T\).  The
intertwining condition is exactly \(A_j\in D\), and the isometry condition
is \(\sum_jA_j^*A_j=1\).  Compressing
\(\operatorname{diag}(X_0,\ldots,X_0)\) gives (HKH2).  Conversely every
column in (HKH2) is such an isometry.

In particular the exact regular-core selector is the finite variational
problem

\[
\Delta^{\rm reg}_{G,B}(X)
 =\operatorname{dist}_{2}\!\left(X,{\cal K}_{G,B}(X_0)\right).       \tag{HKH4}
\]

It has the immediate upper bound

\[
\Delta^{\rm reg}_{G,B}(X)
 \leq\inf_{U\in U(D)}\|X-U^*X_0U\|_2,                 \tag{HKH5}
\]

obtained by taking \(A_1=U\) and \(A_j=0\) for \(j>1\).  Thus the
Selberg-controlled exact endpoint orbit is contained in, but need not
exhaust, the relative ucp window.

There is also an explicit numerical-radius lower bound.  Let \(\tau\) be
normalized matrix trace and \(E_D:B(H)\to D\) the trace-preserving
conditional expectation.  For selfadjoint \(Y\in B(H)\), define

\[
T_Y:L^2(D,\tau)\longrightarrow L^2(D,\tau),\qquad
T_Y(A)=E_D(X_0AY).                                     \tag{HKH6}
\]

The operator \(T_Y\) is selfadjoint.  Indeed, for \(A,C\in D\),

\[
\langle C,T_YA\rangle
 =\tau(C^*X_0AY)
 =\tau(YC^*X_0A)
 =\langle T_YC,A\rangle .                              \tag{HKH7}
\]

If \(Z=\sum_jA_j^*X_0A_j\in{\cal K}_{G,B}(X_0)\), then

\[
\tau(YZ)
 =\sum_j\langle A_j,T_YA_j\rangle
 \leq\lambda_{\max}(T_Y)\sum_j\|A_j\|_2^2
 =\lambda_{\max}(T_Y).                                 \tag{HKH8}
\]

Therefore, for every selfadjoint \(X\) and every selfadjoint
\(Y\) with \(\|Y\|_2\leq1\),

\[
\Delta^{\rm reg}_{G,B}(X)
 \geq
 \bigl(\tau(YX)-\lambda_{\max}(T_Y)\bigr)_+.            \tag{HKH9}
\]

Everything in (HKH9) is finite-level linear algebra in the commutant \(D\).
It is stronger than scalar character separation whenever a noncentral
\(Y\) gives a positive gap.

For the regular congruence Iwahori core take \(G=A_N\), \(B=B_N\).
Formula (HKH4) is the exact finite Hecke--Kraus version of the Stiefel
quantity in (UIR8).  Proving that it tends to zero for every supplied
regular microstate would produce the finite corners and, by property
\((T;FD)\), the flexible endpoint.  No uniform estimate of that kind is
currently known; (HKH9) supplies a concrete way to search for a genuine
moving-level obstruction, but does not assert one.  The root remains open.
