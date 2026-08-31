---
rg: 2
id: jacobson-d8-polar-qutrit-block-table-proof
kind: proof
title: Factor the D8 range trace and audit the ordered phase covariances
target: jacobson-d8-polar-has-flat-nine-phase-first-row
requires:
  - jacobson-d8-spectral-polar-splits-residual-without-qutrit-selection
  - qutrit-shortest-tk-word-graphs-are-diagonal-or-complete
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
---

# Factor the D8 range trace and audit the ordered phase covariances

Write
\[
 F_q=\langle J,X_1,Z_1,X_2,Z_2\rangle,\qquad
 C=\langle J,Z_1\rangle.
\]
The first group is the order-\(3^5\) affine qutrit packet on the twenty-seven
leaves, and the second is its order-nine phase subgroup.  For
\(\rho,a\in\mathbb F_3\), let
\[
 z_{\rho,a}={1\over9}\sum_{j,l\in\mathbb F_3}
 \omega^{-\rho j-al}J^jZ_1^l.                          \tag{JQB5}
\]
These are the nine pairwise orthogonal character atoms of \(C\), with
\[
 Jz_{\rho,a}=\omega^\rho z_{\rho,a},\qquad
 Z_1z_{\rho,a}=\omega^a z_{\rho,a}.                     \tag{JQB6}
\]
The three atoms in the claim are \(e_a=z_{1,a}\).

## 1. Trace factorization for each polar range

Let \(N\) be the elementary abelian two-group whose signed character
projection is the residual \(e\), and put
\[
 M=\langle N,t,kNk\rangle.
\]
The exact polar formula gives
\[
 f_\eta=V_\eta V_\eta^*
        =2p_\eta k e k p_\eta\in\mathbb C[M],
 \qquad p_\eta={1+\eta t\over2}.                        \tag{JQB7}
\]
Every element of \(M\) is the identity outside the three active outer
coordinates.  A nonidentity element of \(F_q\), in the affine realization
on \(\mathbb F_3^2\times\mathbb F_3\), has either no fixed leaf or exactly
nine fixed leaves.  It therefore moves at least eighteen leaves.  Hence
\[
 F_q\cap M=\{1\}.                                       \tag{JQB8}
\]

For \(x\in\mathbb C[F_q]\) and \(y\in\mathbb C[M]\), the identity
coefficient of \(xy\) can only be the product of the two identity
coefficients: if \(gm=1\), then \(g=m=1\) by (JQB8).  Thus
\[
 \tau(xy)=\tau(x)\tau(y).                               \tag{JQB9}
\]
The D8 Gram identity says \(V_\eta^*V_\eta=e\), so
\[
 \tau(f_\eta)=\tau(e)={1\over32}.                       \tag{JQB10}
\]
Each atom in (JQB5) has trace \(1/9\).  Combining (JQB9) and (JQB10),
\[
\begin{aligned}
 \|z_{\rho,a}V_\eta e\|_2^2
 &=\tau(V_\eta^*z_{\rho,a}V_\eta)\\
 &=\tau(z_{\rho,a}f_\eta)
 ={1\over9}\,{1\over32}
 ={1\over288}.                                         \tag{JQB11}
\end{aligned}
\]
Here \(V_\eta e=V_\eta\).  This proves nonvanishing and the first assertion
for all nine phase atoms at once.

For distinct atoms \(z_\lambda,z_\mu\),
\[
 (z_\lambda V_\eta)^*(z_\mu V_\eta)
 =V_\eta^*z_\lambda z_\mu V_\eta=0.
\]
Summing over all nine atoms and using \(\sum_\lambda z_\lambda=1\) gives
\[
 \sum_\lambda(z_\lambda V_\eta)^*(z_\lambda V_\eta)
 =V_\eta^*V_\eta=e.                                    \tag{JQB12}
\]
Thus the equal trace entries are not an incomplete marginal calculation:
they form the full orthogonal phase decomposition of the source Gram
operator.

## 2. The ordered occurrence covariance

Equation (JQB6) immediately gives
\[
 J(e_aV_\eta)=\omega e_aV_\eta,\qquad
 Z_1(e_aV_\eta)=\omega^a e_aV_\eta.                     \tag{JQB13}
\]
Also \(t p_\eta=\eta p_\eta\), whence
\[
 tV_\eta=\eta V_\eta
 \quad\hbox{and therefore}\quad
 e_atV_\eta=\eta e_aV_\eta.                             \tag{JQB14}
\]
Equations (JQB11), (JQB13), and (JQB14) are exactly the three rows of
(JQB2).

The order in (JQB14) matters.  It does not permit moving \(t\) across
\(e_a\).  Indeed the next calculation shows that \(t\) either mixes all
three qutrit phases or preserves them separately, according to the chosen
outer labels.  Thus (JQB14) is an occurrence-typed row identity, not a
claim that the qutrit corner reduces \(t\).

## 3. The bare raw-\(T\) phase graph

For completeness, let \(P\) be a scalar permutation matrix in \(C\).
With \(t=1+TE_{23}\), comparison of the linearly independent Jacobson
normal forms \(1,T,T^2\) in \(tPt\) shows
\[
 tPt\ \hbox{is scalar}
 \quad\Longleftrightarrow\quad
 P\ \hbox{fixes coordinates \(2\) and \(3\) separately}. \tag{JQB15}
\]
Therefore
\[
 C\cap tCt=C_2\cap C_3,                                \tag{JQB16}
\]
the common point stabilizer of the two outer coordinates.

On a qutrit leaf \((u_1,u_2,s)\), the element \(J^cZ_1^b\) adds
\(c-bu_1\) to \(s\).  Its point stabilizer is
\[
 C_{u_1}=\{J^{bu_1}Z_1^b:b\in\mathbb F_3\}\cong C_3.   \tag{JQB17}
\]
Two different \(u_1\)-labels give trivial common stabilizer; equal labels
give the same group (JQB17).  The extra coordinate is fixed by all of
\(C\), so pairing it with a leaf again gives the leaf stabilizer.

The standard character double-coset calculation now says
\[
 e_bt e_a=0
 \quad\hbox{unless}\quad
 \chi_b|_H=\chi_a|_H,\qquad
 \|e_bt e_a\|_2^2={|H|\over81}                         \tag{JQB18}
\]
when the restrictions agree, where \(H=C_2\cap C_3\).  If \(H=1\), all
nine blocks occur and have squared norm \(1/81\).  If \(H=C_{u_1}\), its
generator \(J^{u_1}Z_1\) has values
\[
 \chi_a(J^{u_1}Z_1)=\omega^{u_1+a}.
\]
The three restrictions are distinct, so exactly the diagonal blocks occur,
each with squared norm \(1/27\).

## 4. Hall audit

Orthogonality of \(e_0,e_1,e_2\) and (JQB11) give
\[
 \|RV_\eta\|_2^2={2\over288}={1\over144},\qquad
 \|(q-R)V_\eta\|_2^2={1\over288}.                       \tag{JQB19}
\]
This is the desired unequal marginal, but not the desired incidence.
Every block \(e_aV_\eta\) is nonzero.  In the complete case the two
selected vertices have all three target neighbors; in the diagonal case
they have the two distinct neighbors \(e_0,e_1\).  Their neighbor set never
has cardinality one.  Finally, (JQB14) preserves each already-cut ordered
row and supplies no identification of \(a=0,1\) with \(a=2\).

Hence neither sign branch, neither outer-coordinate labeling, nor the raw
\(t\)-word phase graph authenticates a two-to-one qutrit correspondence.
This proves the balanced no-go claimed for the entire first row.
