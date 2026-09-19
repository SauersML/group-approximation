---
rg: 2
id: stinespring-components-give-frame-energy-and-dual-transport
kind: route
title: Resolve relative positive-definite tables into Kraus frames and transport the separator
target: multi-kraus-frame-energy-is-the-full-relative-pd-gate
requires:
  - relative-pd-body-has-table-or-separator-dichotomy
  - relative-table-separator-is-cayley-cocycle-obstruction
---

# Every relative table has a finite regular Stinespring frame

Let \(F:G\to M_d\) be positive definite, \(F(e)=1\), and
\(F(b)=\beta(b)\) for \(b\in B\). Finite-dimensional Stinespring theory gives
a unitary representation \(\rho:G\to U(\mathscr H)\) and an isometry
\(V:\mathbb C^d\to\mathscr H\) such that
\[
 F(k)=V^*\rho(k)V.                                        \tag{1}
\]
Because the compression \(V^*\rho(b)V=\beta(b)\) is itself unitary, equality
holds in the contraction inequality and
\[
 \rho(b)V=V\beta(b).                                      \tag{2}
\]
Every representation of a finite group embeds in a sufficiently large
amplification \(\lambda_G\otimes1_r\) of the left regular representation.
After such an equivariant embedding, write
\[
 V\xi=\sum_{g\in G}e_g\otimes A_g\xi.                     \tag{3}
\]
The isometry equation gives the first identity in (MKF2). Comparing the
\(e_g\)-components of
\((\lambda_G(b)\otimes1)V=V\beta(b)\) gives
\[
 A_{bg}=A_g\beta(b)^*.                                    \tag{4}
\]
Finally,
\[
 V^*(\lambda_G(k)\otimes1)V
 =\sum_g A_{kg}^*A_g=F(k),                                \tag{5}
\]
which is (MKF3).

Conversely, a family satisfying (MKF2) defines by (3) an isometry into
\(\ell^2(G)\otimes\mathbb C^r\). Equation (5) makes \(F_A\) positive
definite and normalized. Equation (4) gives
\[
 F_A(b)=\sum_g\beta(b)A_g^*A_g=\beta(b).                  \tag{6}
\]
This proves the exact frame parametrization of the full relative body.

# Energy is coefficient distance plus compression leakage

For a fixed marked row \(s\), expansion of the square in (MKF4) and the two
reindexed copies of \(\sum_gA_g^*A_g=1\) give
\[
 \sum_g\frac1d\|A_{sg}U_s-A_g\|_{\mathrm F}^2
 =2-2\operatorname{Re}\operatorname{tr}_d(U_s^*F_A(s)).
                                                                    \tag{7}
\]
Since a normalized positive-definite coefficient is a contraction,
\[
 \begin{aligned}
 2-2\operatorname{Re}\operatorname{tr}_d(U_s^*F_A(s))
 &=\|U_s-F_A(s)\|_{2,d}^2+1-\|F_A(s)\|_{2,d}^2,           \tag{8}
 \end{aligned}
\]
and the final term is nonnegative. Averaging (8) proves
\(\Delta(U)\leq\mathcal E_U^{\mathrm K}(A)\), hence the first inequality in
(MKF5).

Choose a coefficient table attaining \(\Delta(U)\) and resolve it by the
first part. Put \(a_s=\|U_s-F_A(s)\|_{2,d}\). The contraction bound and
Cauchy--Schwarz give
\[
 \begin{aligned}
 0\leq1-\|F_A(s)\|_{2,d}^2
 &=\operatorname{Re}\operatorname{tr}_d
   \big((U_s-F_A(s))^*U_s+F_A(s)^*(U_s-F_A(s))\big)\\
 &\leq2a_s.                                               \tag{9}
 \end{aligned}
\]
Therefore
\[
 \mathcal E_U^{\mathrm K}(A)^2
 \leq\Delta(U)^2+\frac2{|S|}\sum_sa_s
 \leq\Delta(U)^2+2\Delta(U),                              \tag{10}
\]
which finishes (MKF5)--(MKF7).

# The normal vector has an isometric Kraus transport

For every \(s\), reindexing the frame normalization gives
\[
 U_s-F_A(s)
 =\sum_gA_{sg}^*(A_{sg}U_s-A_g).                          \tag{11}
\]
Pairing (11) with \(Z_s\), using cyclicity of trace, and averaging proves
(MKF8). Moreover,
\[
 \begin{aligned}
 \frac1{|S|}\sum_{s,g}\frac1d\|A_{sg}Z_s\|_{\mathrm F}^2
 &=\frac1{|S|}\sum_s
   \operatorname{tr}_d\left(Z_s^*
     \left(\sum_gA_{sg}^*A_{sg}\right)Z_s\right)\\
 &=\frac1{|S|}\sum_s\|Z_s\|_{2,d}^2=1.                   \tag{12}
 \end{aligned}
\]
If \(Z\) separates \(U\) from the relative body by \(\delta\), then
\(F_A\) is feasible, so the left side of (MKF8) is at least \(\delta\).
Cauchy--Schwarz with (12) proves (MKF10).

For a unitary zero-cochain \(W\) from (RCO2), the special choice
\[
 A_g=|G|^{-1/2}W_g^*
\]
is a flat square frame after the harmless left/right convention is aligned.
General frames have arbitrary target dimension and nonconstant positive
Gram operators \(A_g^*A_g\). Hence the unitary Cayley problem is a strict
subproblem unless one separately proves a dimension-free polar flattening
theorem. The identities above use the complete Stinespring class and
therefore exactly match the convex body, without making that unsupported
flattening step.
