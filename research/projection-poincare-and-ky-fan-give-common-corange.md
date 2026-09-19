---
rg: 2
id: projection-poincare-and-ky-fan-give-common-corange
kind: route
title: Combine projection Poincare, Ky Fan rounding, and equivariant polar synchronization
target: cayley-expansion-aligns-isometry-frame-coranges
requires:
  - right-translation-flattens-every-relative-kraus-frame
  - tfd-finite-corner-collapse-and-rfd-firewall
---

# Projection motion is controlled by isometry-row motion

Fix an edge \((s,g)\), and put
\[
 A=V_{sg}U_s,\qquad B=V_g,\qquad C=A^*B.
\]
Both \(A\) and \(B\) are isometries, and their range projections are
\(P_{sg}\) and \(P_g\). Therefore
\[
 \|P_{sg}-P_g\|_{\mathrm F}^2
 =2d-2\|C\|_{\mathrm F}^2,                                \tag{1}
\]
whereas
\[
 \|A-B\|_{\mathrm F}^2=2d-2\operatorname{Re}\operatorname{Tr}C. \tag{2}
\]
The nonnegative square
\[
 0\leq\|C-1\|_{\mathrm F}^2
 =\|C\|_{\mathrm F}^2+d-2\operatorname{Re}\operatorname{Tr}C
\]
gives
\[
 \|P_{sg}-P_g\|_{\mathrm F}^2
 \leq2\|V_{sg}U_s-V_g\|_{\mathrm F}^2.                    \tag{3}
\]
The singular values of \(C\) are
\(\cos\theta_1(s,g),\ldots,\cos\theta_d(s,g)\), so (1) is
the equality in (CEA6). Notice that (3) is dimension-free and allows
arbitrary ambient \(R\).

# The average range operator has a nearby rank-d plane

Put
\[
 \overline P=\frac1{|G|}\sum_gP_g.
\]
Applying (CEA1) to the Hilbert--Schmidt-valued function \(g\mapsto P_g\)
and then using (3) gives
\[
 \begin{aligned}
 \frac1{|G|d}\sum_g\|P_g-\overline P\|_{\mathrm F}^2
 &=1-\frac1d\operatorname{Tr}(\overline P^2)\\
 &\leq\frac2\gamma e(V)^2.                               \tag{4}
 \end{aligned}
\]
Let
\[
 1\geq\lambda_1\geq\cdots\geq\lambda_R\geq0
\]
be the eigenvalues of \(\overline P\). Their sum is \(d\). Let \(P\)
be the spectral projection onto the top \(d\) eigenvectors and put
\[
 t=\sum_{i>d}\lambda_i=\sum_{i\leq d}(1-\lambda_i).        \tag{5}
\]
There is a useful sharp ordering estimate
\[
 t\leq d-\operatorname{Tr}(\overline P^2).                \tag{6}
\]
Indeed, write \(a_i=1-\lambda_i\) for \(i\leq d\) and
\(b_j=\lambda_{d+j}\). Both families have sum \(t\), while
\[
 \max_i a_i+\max_j b_j
 =1-\lambda_d+\lambda_{d+1}\leq1.
\]
Hence
\[
 \sum_i a_i^2+\sum_jb_j^2
 \leq t(\max_i a_i+\max_jb_j)\leq t.
\]
But
\[
 d-\operatorname{Tr}(\overline P^2)
 =2t-\sum_i a_i^2-\sum_jb_j^2,
\]
which proves (6).

Ky Fan maximality and (5)--(6) now give
\[
 \begin{aligned}
 \eta
 &:=\frac1{|G|d}\sum_g\operatorname{Tr}((1-P)P_g)\\
 &=\frac1d\operatorname{Tr}((1-P)\overline P)
 =\frac td
 \leq\frac2\gamma e(V)^2.                                \tag{7}
 \end{aligned}
\]
This is (CEA7).

# Compression to the common plane polarizes equivariantly

Choose an isometry \(J:\mathbb C^d\to\mathbb C^R\) with \(JJ^*=P\), and
define the contractions
\[
 C_g=J^*V_g\in M_d.
\]
They retain both the row and relative identities:
\[
 \|C_{sg}U_s-C_g\|_{2,d}
 \leq\|V_{sg}U_s-V_g\|_{2,d},\qquad
 C_{bg}=C_g\beta(b)^*.                                    \tag{8}
\]
On one representative of each left \(B\)-coset, take a unitary extension
\(Q_g\) of the polar partial isometry of \(C_g\), and extend it by
\[
 Q_{bg}=Q_g\beta(b)^*.                                    \tag{9}
\]
This is a polar extension of \(C_{bg}\). Since every singular value
\(\sigma\) of \(C_g\) lies in \([0,1]\),
\[
 \begin{aligned}
 \|C_g-Q_g\|_{2,d}^2
 &=\frac1d\sum_j(1-\sigma_j(C_g))^2\\
 &\leq\frac1d\sum_j(1-\sigma_j(C_g)^2)
 =\frac1d\operatorname{Tr}((1-P)P_g).                    \tag{10}
 \end{aligned}
\]
Thus the RMS polar error is at most \(\sqrt\eta\).

Put \(W_g=Q_g^*\). Equation (9) gives
\(W_{bg}=\beta(b)W_g\), and
\[
 \|U_sW_g-W_{sg}\|_{2,d}
 =\|Q_{sg}U_s-Q_g\|_{2,d}.                                \tag{11}
\]
Minkowski's inequality in the direct sum over \(S\times G\), followed by
(8) and (10), yields
\[
 \mathcal E_U(W)\leq e(V)+2\sqrt\eta
 \leq\left(1+2\sqrt{\frac2\gamma}\right)e(V).              \tag{12}
\]
Right-multiplying every \(W_g\) by \(W_e^*\) preserves (9), (11), and the
energy, and normalizes \(W_e=1\). This proves (CEA4)--(CEA5).

Taking infima gives (CEA8), because every unitary table is an isometry
table with \(R=d\). Equations (RTF7)--(RTF8) then give (CEA9).

# Property TFD supplies the needed quotient gap

Let \(\Gamma=\langle S\rangle\) have property \((T;FD)\), and let
\(G\) be any finite quotient with the induced marked set. For
\(f:G\to\mathcal H\), the left-translation action on
\(\ell^2(G)\otimes\mathcal H\) is finite-dimensional. Its invariant
subspace consists exactly of the constant functions. The uniform
finite-dimensional Kazhdan gap, applied on the orthogonal complement,
is precisely (CEA1), after fixing the displayed normalization. Hence one
\(\gamma>0\) works for all finite quotients and every finite target
dimension \(R\). This includes the forced authenticated quotients \(A_N\).

# Why expansion cannot be omitted from framewise alignment

For (CEA10), both marked edge lengths are
\[
 \|V_{j\pm1}-V_j\|^2=4\sin^2(\pi/L),
\]
so \(e(V)=2\sin(\pi/L)\). Direct trigonometric averaging gives
\[
 \frac1L\sum_jV_jV_j^*=\frac12I_2.
\]
For any rank-one projection \(P\),
\[
 \frac1L\sum_j\operatorname{Tr}((1-P)V_jV_j^*)=\frac12.
\]
Thus no estimate of the form (CEA7) with a quotient-independent constant
can hold on arbitrary Cayley graphs. The example has a separate constant
unitary zero-cochain of energy zero, so it attacks only framewise
common-corange rounding and makes no claim against the infimum comparison
under expansion.
