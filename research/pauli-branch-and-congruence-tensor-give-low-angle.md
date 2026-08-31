---
rg: 2
id: pauli-branch-and-congruence-tensor-give-low-angle
kind: route
title: Compute the Pauli restriction Jacobian and preserve it under congruence tensoring
target: regular-trace-does-not-bound-iwahori-word-jacobian
requires:
  - iwahori-nielsen-hs-bilipschitz
  - residual-finite-tensor-camouflages-iwahori-transfer-failures
---

# The Pauli branch and its regular tensor camouflage

## 1. The Iwahori word differential

Put
\[
 X=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
 U_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\
                          \sin\theta& \cos\theta\end{pmatrix},
\]
let \(\omega=\exp(2\pi i/3)\), and set
\[
 A_\theta=U_\theta
 \begin{pmatrix}\omega&0\\0&\overline\omega\end{pmatrix}
 U_\theta^*.
                                                               \tag{1}
\]
Then \(X^2=A_\theta^3=1\), so
\(\rho_\theta(x)=X,\rho_\theta(a)=A_\theta\) is an exact representation of
\(C_2*C_3\).

Use right-logarithmic tangent coordinates
\[
 \dot X=K_XX,\qquad \dot A=K_AA
\]
with \(K_X,K_A\) anti-Hermitian. Differentiating the torsion equations gives
\[
 (1+\operatorname{Ad}X)K_X=0,\qquad
 (1+\operatorname{Ad}A+\operatorname{Ad}A^2)K_A=0.       \tag{2}
\]
For the Iwahori words
\[
 U=XA,\qquad E=AXA^{-1},
\]
right-logarithmic differentiation gives the exact linear map
\[
 J_\theta(K_X,K_A)=
 \left(
 K_X+\operatorname{Ad}X(K_A),\
 \operatorname{Ad}A(K_X)+(1-\operatorname{Ad}E)(K_A)
 \right).                                                \tag{3}
\]
This is \(d\operatorname{Res}_{\rho_\theta}\).

## 2. Exact singular calculation

Let
\[
 B_1={1\over\sqrt2}\begin{pmatrix}0&1\\-1&0\end{pmatrix},
 \qquad
 B_2={1\over\sqrt2}\begin{pmatrix}0&i\\ i&0\end{pmatrix}.
\]
An orthonormal real basis of the domain in (2) is
\[
 (B_1,0),\ (B_2,0),\
 (0,U_\theta B_1U_\theta^*),\
 (0,U_\theta B_2U_\theta^*).                             \tag{4}
\]
Substitution of (1) and (4) into (3), using the Frobenius inner product,
gives
\[
 \det(J_\theta^*J_\theta)
 =3\cos^2(2\theta)\bigl(5-2\cos^2(2\theta)\bigr).         \tag{5}
\]
This is a direct four-by-four Pauli-matrix multiplication; no limiting
argument is used.

For \(0\leq\theta\leq\pi/2\), equation (5) shows that \(J_\theta\) is
injective except at \(\theta=\pi/4\). Real rotations commute with \(B_1\),
so the unit domain vector
\[
 v_\theta=2^{-1/2}(B_1,B_1)                              \tag{6}
\]
belongs to (2) for every \(\theta\). A second direct substitution gives
\[
 \|J_\theta v_\theta\|
 =\sqrt{3/2}\,|\cos(2\theta)|.                           \tag{7}
\]
For \(\theta\neq\pi/4\), (7) proves (RTJ2). At
\(\theta=\pi/4\), (6) spans the kernel, because (5) vanishes to order two
and the other three Pauli columns are independent.

Normalized Hilbert--Schmidt norms give the same singular values: the common
factor \(2^{-1/2}\) occurs in both domain and range.

## 3. Tensoring makes the trace regular without repairing the angle

Choose odd congruence quotients
\[
 q_n:V\longrightarrow Q_n
\]
which separate every fixed nonidentity element, and let
\(\lambda_{Q_n}\) be their left regular representations. For
\(\theta_n\to\pi/4\), \(\theta_n\neq\pi/4\), define (RTJ3). For fixed
\(g\in V\),
\[
 \operatorname{tr}(\Pi_n(g))
 =\operatorname{tr}(\rho_{\theta_n}(g))\,
   1_{\{q_n(g)=e\}}
 \longrightarrow\delta_{g,e}.                           \tag{8}
\]
The order-two and order-three elements act without fixed points in the
regular quotient, so their spectral multiplicities are exactly balanced.

The Hilbert space of matrix coefficients contains the reducing sector
\[
 M_2\otimes\mathbb C1.
\]
Every adjoint generator preserves this sector and its orthogonal complement.
On tangent vectors
\[
 (K_X\otimes1,K_A\otimes1)
\]
the torsion constraints and the restriction differential are exactly (2)
and (3), tensored with \(1\). Both input and output normalized
Hilbert--Schmidt norms acquire the same factor. Moreover (B_1) is
invertible, so the witness (B_1\otimes1) has full physical support and
uniformly bounded operator norm. Hence every singular value
of \(J_{\theta_n}\) occurs in the full tensor-product differential, and
\[
 s_{\min}^{+}(d\operatorname{Res}_{\Pi_n})
 \leq \sqrt{3/2}\,|\cos(2\theta_n)|\longrightarrow0.      \tag{9}
\]

Finally, pullback by \(\alpha\) is the fixed word-coordinate map recorded in
**iwahori-nielsen-hs-bilipschitz**. Its differential and inverse have
dimension-independent norm bounds. Applying it to (9) preserves vanishing
of the singular value.

The construction diagnoses the wrong linear target. It does not place the
two vertices at a common compatible endpoint, so it does not contradict the
Mayer--Vietoris gap there and cannot by itself be integrated into a global
capture counterexample.
