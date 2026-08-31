---
rg: 2
id: crossed-product-pvm-coefficient-gram-and-quarter-bound-proof
kind: route
title: Crossed-product PVM coefficient Gram equations and the quarter-overlap bound
target: actor-fourier-mixing-is-the-naimark-defect-of-the-base-povm
requires:
  - perfect-qc-separation-yields-finite-bcs-with-no-matrix-model
  - orthogonal-steinberg-root-spectral-support-is-not-additive
  - shared-center-extraspecial-wreath-has-fd-invisible-spin-sector
  - leavitt-root-signs-cannot-host-the-perfect-synchbcs
---

# Crossed-product PVM coefficient Gram equations and the quarter-overlap bound

## 1. Conventions and coefficient equations

Let \(B\) sit faithfully in a finite von Neumann algebra with trace \(\tau\),
and let \(G\) act by trace-preserving star automorphisms \(\alpha_g\). We use

\[
 u_gbu_g^*=\alpha_g(b).
\]

Thus multiplication and adjoint in the algebraic crossed product are

\[
 (a_gu_g)(b_hu_h)=a_g\alpha_g(b_h)u_{gh},
 \qquad
 (a_gu_g)^*=\alpha_{g^{-1}}(a_g^*)u_{g^{-1}}.              \tag{1}
\]

Write a finite-support self-adjoint element as

\[
 P_i=\sum_g a_{i,g}u_g.
\]

Comparing the coefficient of \(u_{g^{-1}}\) in \(P_i^*=P_i\) gives

\[
 a_{i,g^{-1}}=\alpha_{g^{-1}}(a_{i,g}^*).                  \tag{2}
\]

If \(P_iP_j=\delta_{ij}P_i\), the coefficient of \(u_k\) is

\[
 \sum_{gh=k}a_{i,g}\alpha_g(a_{j,h})
 =\delta_{ij}a_{i,k}.                                      \tag{3}
\]

Equations (2)--(3), together with finite support, are the complete algebraic
projection/PVM equations. There is no hidden convergence issue.

## 2. The identity coefficient is a POVM and its defect is a Gram matrix

Set

\[
 A_i=a_{i,1}=E_B(P_i).
\]

Conditional expectation is unital and positive. Hence each \(A_i\) is a
positive contraction. If \(\sum_iP_i=1\), coefficient comparison gives

\[
 \sum_iA_i=1,\qquad
 \sum_i a_{i,g}=0\quad(g\ne1).                             \tag{4}
\]

Thus \((A_i)\) is a POVM.

Put \(k=1\) in (3). Then \(h=g^{-1}\), so (2) gives

\[
 \alpha_g(a_{j,g^{-1}})
 =\alpha_g\!\left(\alpha_{g^{-1}}(a_{j,g}^*)\right)
 =a_{j,g}^*.
\]

Separating the \(g=1\) term proves the operator identity

\[
 \delta_{ij}A_i-A_iA_j
 =\sum_{g\ne1}a_{i,g}a_{j,g}^*.                            \tag{5}
\]

For \(i=j\),

\[
 A_i-A_i^2=\sum_{g\ne1}a_{i,g}a_{i,g}^*\ge0.               \tag{6}
\]

Taking the trace yields the exact Parseval/variance identity

\[
 \sum_{g\ne1}\|a_{i,g}\|_2^2
 =\tau(A_i-A_i^2).                                         \tag{7}
\]

If \(A_i\) is a projection, the left side of (6) is zero. Every summand on
the right is positive, so every \(a_{i,g}\) for \(g\ne1\) is zero. Therefore

\[
 E_B(P_i)\text{ is a projection}
 \quad\Longrightarrow\quad
 P_i=E_B(P_i)\in B.                                        \tag{8}
\]

The converse is immediate. This is the coefficient-level multiplicative
domain statement, with the complete actor-mass identity retained.

## 3. Orthogonality requires base variance

Let \(P,Q\) be orthogonal projections and write their coefficients as
\((a_g)\) and \((b_g)\), with

\[
 A=E_B(P),\qquad B_0=E_B(Q).
\]

The off-diagonal case of (5) says

\[
 AB_0=-\sum_{g\ne1}a_gb_g^*.                              \tag{9}
\]

Because \(A,B_0\ge0\), traciality gives

\[
 \tau(AB_0)
 =\tau(A^{1/2}B_0A^{1/2})\ge0.
\]

Apply Cauchy--Schwarz to the finite coefficient rows in (9):

\[
\begin{aligned}
 \tau(AB_0)
 &\leq
 \left(\sum_{g\ne1}\|a_g\|_2^2\right)^{1/2}
 \left(\sum_{g\ne1}\|b_g\|_2^2\right)^{1/2}\\
 &=\sqrt{\tau(A-A^2)\tau(B_0-B_0^2)}.                     \tag{10}
\end{aligned}
\]

This is (AFM4). In particular, a positive base overlap can be cancelled only
by nonzero actor variance on both rows.

## 4. Quantitative specialization to the marked quarter overlap

Let \(Q_e,Q_f\) be the two commuting root-cut projections from the
\(\mathbf F_2\times\mathbf F_2\) model. Their normalized trace satisfies

\[
 \tau(Q_eQ_f)=\frac14.                                     \tag{11}
\]

Assume

\[
 \|A-Q_e\|_2\leq\varepsilon_e,\qquad
 \|B_0-Q_f\|_2\leq\varepsilon_f.                           \tag{12}
\]

Since \(A,B_0,Q_e,Q_f\) are contractions,

\[
\begin{aligned}
 \left|\tau(AB_0)-\tau(Q_eQ_f)\right|
 &\leq
 \left|\tau((A-Q_e)B_0)\right|
 +\left|\tau(Q_e(B_0-Q_f))\right|\\
 &\leq\varepsilon_e+\varepsilon_f.
\end{aligned}                                              \tag{13}
\]

We also need a variance estimate. For any positive contraction \(C\), any
projection \(Q\), and \(\|C-Q\|_2\leq\varepsilon\),

\[
\begin{aligned}
 \tau(C-C^2)
 &\leq |\tau(C-Q)|+|\tau(C^2-Q)|\\
 &\leq \varepsilon+
       |\tau(C(C-Q))|+|\tau((C-Q)Q)|\\
 &\leq3\varepsilon.                                        \tag{14}
\end{aligned}
\]

Here we used the exact identity
\(C^2-Q=C(C-Q)+(C-Q)Q\).

Combining (10)--(14) proves

\[
 \frac14-\varepsilon_e-\varepsilon_f
 \leq3\sqrt{\varepsilon_e\varepsilon_f}.                   \tag{15}
\]

If both errors are at most \(\varepsilon\), then

\[
 \frac14-2\varepsilon\leq3\varepsilon,
\]

and therefore

\[
 \varepsilon\geq\frac1{20}.                                \tag{16}
\]

The constant is not asserted optimal. Its role is that it is positive and
independent of matrix dimension, actor support size, and the ambient spin
window.

At the exact endpoint, (8) is stronger: if \(A=Q_e\) and \(B_0=Q_f\), then
\(P=Q_e\) and \(Q=Q_f\), contradicting orthogonality by (11).

## 5. The scalar two-point absorber shows what the equations allow

Let \(G=C_2=\langle u\rangle\), let \(B=\mathbf C\), and use the trivial
action. Define

\[
 P_+=\frac{1+u}{2},\qquad P_-=\frac{1-u}{2}.                \tag{17}
\]

Then \(P_+,P_-\) are orthogonal projections summing to one. Their identity
coefficients are both \(1/2\), while their \(u\)-coefficients are \(1/2\)
and \(-1/2\). Thus

\[
 \frac12-\left(\frac12\right)^2
 =\left|\frac12\right|^2,
 \qquad
 \frac14+\left(\frac12\right)\left(-\frac12\right)=0.       \tag{18}
\]

Equations (6) and (9) are sharp on this cell: actor Fourier mass cancels the
base overlap exactly. But \(\mathbf C[C_2]\) is two-dimensional, so this is
a finite absorber, not a nonmatricial occurrence gadget.

The same point is intrinsic to one context. A PVM by itself generates the
finite-dimensional commutative algebra spanned by its atoms. In the
shared-center host, all of its finitely many identity coefficients lie in one
finite spin block. Their POVM has an ordinary finite-dimensional Naimark
dilation. Therefore neither the presence of actor coefficients nor the
single-context Gram equations can carry the non-CE obstruction. Only the
simultaneous identification of effects across several contexts can do so.

## 6. Application to the full shared-center negative corner

For the shared-center extraspecial base, put

\[
 B_{\mathrm{spin}}=p_-\mathbf C[E(X)]p_-.
\]

The actor fixes \(p_-\) and permutes the named spin tensor legs, so

\[
 p_-\mathbf C[E(X)\rtimes G]p_-
 \cong B_{\mathrm{spin}}\rtimes_{\mathrm{alg}}G.            \tag{19}
\]

The normalized canonical negative-corner trace is precisely the
\(G\)-invariant tensor trace on the base followed by the identity Fourier
coefficient. Hence Sections 1--5 apply literally.

Suppose one tries to repair the root-cut overlap by choosing mixed
projections \(P_e,P_f\) but insists on

\[
 E_{B_{\mathrm{spin}}}(P_e)=Q_e,\qquad
 E_{B_{\mathrm{spin}}}(P_f)=Q_f.                           \tag{20}
\]

Equation (8) deletes every actor coefficient, and (11) refutes
orthogonality. If (20) is weakened to approximate port preservation, (16)
forces movement by at least \(1/20\) on one of the two identity coefficients.

Thus a surviving construction cannot regard actor terms as invisible
corrections behind fixed sharp Pauli ports. It must replace the ports by
unsharp effects and solve all the matrix-valued Gram identities (5)
simultaneously over the context-incidence graph. The scalar cell (17) warns
that any finite actor return merely gives another matrix dilation. To escape,
the shared rows must consume the non-finitely-completable Kun--Thom marked
compressor pattern.

This proof supplies necessary equations and a finite-support local no-go. It
does not construct the required global atlas, and it does not establish a
nonhyperlinear group.
