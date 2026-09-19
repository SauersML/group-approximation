---
rg: 2
id: exact-inversion-transfer-is-twisted-coboundary
kind: claim
title: Exact inversion turns the regular Hecke transfer into a twisted coboundary Laplacian
distinct_from:
  regular-core-window-is-a-hecke-kraus-hull: that parametrizes every relative window and introduces the transfer; this identifies its exact Dirichlet operator after imposing the involution and inversion rows.
  right-regular-multiflips-have-exact-cubic-hole-charge: that solves coverage for gauges in the right group algebra; this treats an arbitrary gauge in the much larger exact right commutant and isolates the missing converse inequality.
  same-core-involution-cubic-gauge-coercivity: that globally controls gauges commuting with the parabolic generator; this keeps only the inversion-forced commutation with the torus generator.
---

Let \((X_0,R,T)\) be a finite-dimensional exact square-free Iwahori
endpoint, with
\[
 X_0^2=1,\qquad X_0RX_0=R^{-1},\qquad
 (X_0T)^3=(X_0T^2R)^3=1.
\]
Write
\[
 D=\{R,T\}',\qquad \theta=\operatorname{Ad}_{X_0},
 \qquad a=X_0T,\qquad b=X_0T^2R,
\]
and let \(E_D\) be the trace-preserving expectation onto \(D\).

Suppose that \(X\) is another involution satisfying the exact inversion
row \(XRX=R^{-1}\), and put
\[
 C=XX_0,\qquad \alpha=\operatorname{Ad}_a,\qquad
 \beta=\operatorname{Ad}_b.                              \tag{TCB1}
\]
Then
\[
 \theta(C)=C^{-1},\qquad [C,R]=0.                        \tag{TCB2}
\]
No commutation of \(C\) with \(T\) is asserted.

Define the twisted coboundary
\[
 d_C:D\longrightarrow L^2(B(H)),\qquad
 d_C(A)=\theta(A)-AC.                                   \tag{TCB3}
\]
For the regular Hecke transfer
\[
 T_X(A)=E_D(X_0AX)
\]
one has the exact operator identity
\[
 2(1-T_X)=d_C^*d_C\quad\hbox{on }L^2(D).                \tag{TCB4}
\]
Consequently
\[
 {\cal H}_\epsilon
 ={\bf1}_{[1-\epsilon,1]}(T_X)L^2(D)
 ={\bf1}_{[0,2\epsilon]}(d_C^*d_C)L^2(D).              \tag{TCB5}
\]
Thus the moving near-top module is exactly the low-energy space of one
finite twisted coboundary, not merely a perturbative spectral band.

The two cubic residuals are its noncommutative curvature holonomies:
\[
 F_\alpha(C):=C\alpha(C)\alpha^2(C)=(XT)^3,
\]
\[
 F_\beta(C):=C\beta(C)\beta^2(C)=(XT^2R)^3.             \tag{TCB6}
\]
For every \(A\in D\), put \(e=d_C(A)\). Since
\(\alpha(A)=\beta(A)=\theta(A)\), the exact propagation identities give
\[
 \|A(F_\alpha(C)-1)\|_2\leq3\|e\|_2,\qquad
 \|A(F_\beta(C)-1)\|_2\leq3\|e\|_2.                    \tag{TCB7}
\]

In particular, if \(A_j\in{\cal H}_\epsilon\) and
\[
 P=\sum_jA_j^*A_j\leq1,
\]
then
\[
 \tau\!\left((F_\alpha-1)^*P(F_\alpha-1)\right)
 \leq18\epsilon,
\qquad
 \tau\!\left((F_\beta-1)^*P(F_\beta-1)\right)
 \leq18\epsilon.                                       \tag{TCB8}
\]
At \(\epsilon=0\), a unital top frame forces both cubic rows to be exact.

The optimal coverage is therefore the finite twisted-coboundary capacity
\[
 c_\epsilon(C)=
 \max\left\{\tau\!\left(\sum_jA_j^*A_j\right):
 A_j\in{\bf1}_{[0,2\epsilon]}(d_C^*d_C)D,\
 \sum_jA_j^*A_j\leq1\right\}.                          \tag{TCB9}
\]
Equations (TCB4)--(TCB9) identify the remaining trace-Cheeger statement
without assuming it: one must construct a nearly unital low-energy
Kraus frame from small \(L^2\)-curvatures \(F_\alpha-1,F_\beta-1\).
The implication (TCB8) runs in the necessary direction only. The
right-regular multiflip sector satisfies the desired converse with an
exact carrier law, while an arbitrary \(R\)-central, non-\(T\)-central
gauge is not settled here. Hence the authenticated regular-core lift and
the non-hyperlinearity root remain open.

DERIVATION
exact-inversion-twisted-coboundary-proof
