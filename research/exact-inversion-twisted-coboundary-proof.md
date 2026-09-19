---
rg: 2
id: exact-inversion-twisted-coboundary-proof
kind: route
title: Factor the transfer defect and propagate it around the two cubic triangles
target: exact-inversion-transfer-is-twisted-coboundary
requires:
  - iwahori-square-free-bs14-presentation
  - regular-core-window-is-a-hecke-kraus-hull
  - hecke-top-spectrum-coverage-controls-window
  - right-regular-multiflips-have-exact-cubic-hole-charge
---

Since \(X=CX_0\) and \(X,X_0\) are involutions,
\[
 \theta(C)=X_0(XX_0)X_0=X_0X=C^{-1}.
\]
Moreover
\[
 CRC^{-1}=XX_0RX_0X=XR^{-1}X=R,
\]
which proves (TCB2). This is exactly where the inversion row is used; it
does not imply \([C,T]=0\).

For \(A\in D\), right multiplication by \(X_0\) gives
\[
 (X_0A-AX)X_0=\theta(A)-AC=d_C(A).                     \tag{TCP1}
\]
Both summands before subtraction have \(2\)-norm \(\|A\|_2\). Therefore
\[
 \|d_C(A)\|_2^2
 =2\|A\|_2^2-2\operatorname{Re}\tau(A^*X_0AX).
\]
The transfer \(T_X\) is selfadjoint because \(X_0\) and \(X\) are
selfadjoint. Hence the last real part is
\(\langle A,T_XA\rangle\), and polarization proves
\(d_C^*d_C=2(1-T_X)\). Functional calculus gives (TCB5).

Because \(A\) commutes with \(T\) and \(T^2R\),
\[
 \alpha(A)=aAa^{-1}=\theta(A),\qquad
 \beta(A)=bAb^{-1}=\theta(A).                           \tag{TCP2}
\]
Also \(a^3=b^3=1\), so direct multiplication yields
\[
 (Ca)^3=C\alpha(C)\alpha^2(C),\qquad
 (Cb)^3=C\beta(C)\beta^2(C),
\]
which is (TCB6).

For the quantitative propagation, first use \(\alpha\) and set
\(e=\alpha(A)-AC=d_C(A)\). Iterating this identity gives
\[
 \alpha^3(A)
 =A\,C\alpha(C)\alpha^2(C)
  +e\alpha(C)\alpha^2(C)
  +\alpha(e)\alpha^2(C)+\alpha^2(e).
\]
Since \(\alpha^3(A)=A\), this is the exact identity
\[
 A(F_\alpha-1)
 =-e\alpha(C)\alpha^2(C)
  -\alpha(e)\alpha^2(C)-\alpha^2(e).                   \tag{TCP3}
\]
Automorphisms and multiplication by unitaries preserve normalized
Hilbert--Schmidt norm, so the first inequality in (TCB7) follows. Equation
(TCP2) says that the initial error for \(\beta\) is the same \(e\); the
identical calculation gives the second inequality.

If \(A_j\in{\cal H}_\epsilon\), (TCB4)--(TCB5) imply
\[
 \sum_j\|d_C(A_j)\|_2^2
 =2\sum_j\langle A_j,(1-T_X)A_j\rangle
 \leq2\epsilon\sum_j\|A_j\|_2^2
 =2\epsilon\tau(P)\leq2\epsilon.                       \tag{TCP4}
\]
On the other hand,
\[
 \sum_j\|A_j(F_\alpha-1)\|_2^2
 =\tau((F_\alpha-1)^*P(F_\alpha-1)).
\]
Squaring (TCB7), summing, and using (TCP4) proves the first half of
(TCB8); the second is identical.

Finally, (TCB5) inserted into the definition of optimal contractive
near-top coverage gives (TCB9). Formula (TCP3) explains the logical
direction sharply: low coboundary energy forces small curvature on the
covered carrier, but small global curvature does not itself manufacture
a low-energy carrier. That missing nonlinear, equivariant decoding step
is precisely the claimed trace-Cheeger problem.
