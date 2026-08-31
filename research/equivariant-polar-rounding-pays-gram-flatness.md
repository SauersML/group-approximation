---
rg: 2
id: equivariant-polar-rounding-pays-gram-flatness
kind: route
title: Polar-round each square relative fibre and pay its Gram defect
target: gram-flat-kraus-frames-polarize-to-unitary-tables
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
  - right-translation-flattens-every-relative-kraus-frame
---

# Equivariant polar choices

For each representative \(g\) of a left \(B\)-coset, take the polar
decomposition of \(B_g\) and extend its polar partial isometry to a unitary
\(Q_g\in U(d)\). Define
\[
 Q_{bg}=Q_g\beta(b)^*,\qquad W_g=Q_g^*.                  \tag{1}
\]
Because \(B_{bg}=B_g\beta(b)^*\), this is a polar extension for every fibre
and \(W_{bg}=\beta(b)W_g\).

The scalar inequality
\[
 (\sqrt t-1)^2\leq|t-1|
\]
and functional calculus give
\[
 \|B_g-Q_g\|_{2,d}^2
 =\operatorname{tr}_d(|B_g|-1)^2
 \leq\operatorname{tr}_d|B_g^*B_g-1|.                   \tag{2}
\]
Hence
\[
 \left(\frac1{|G|}\sum_g\|B_g-Q_g\|_{2,d}^2\right)^{1/2}
 \leq\sqrt{\eta_{\rm gr}(A)}.                           \tag{3}
\]

# The row energy pays two polar errors

Bi-invariance gives
\[
 \|U_sW_g-W_{sg}\|_{2,d}
 =\|Q_{sg}U_s-Q_g\|_{2,d}.                              \tag{4}
\]
Also
\[
 \mathcal E_U^{\rm K}(A)^2
 =\frac1{|S||G|}\sum_{s,g}
   \|B_{sg}U_s-B_g\|_{2,d}^2.                            \tag{5}
\]
For each edge,
\[
 \begin{aligned}
 \|Q_{sg}U_s-Q_g\|_{2,d}
 &\leq\|B_{sg}U_s-B_g\|_{2,d}\\
 &\quad+\|Q_{sg}-B_{sg}\|_{2,d}
       +\|Q_g-B_g\|_{2,d}.                              \tag{6}
 \end{aligned}
\]
Minkowski in the Hilbert direct sum over \(S\times G\), followed by (3)
for the last two terms, proves (GFP3).

# A zero-energy frame need not be square-flat

Schur orthogonality for (GFP4) gives
\[
 \frac d{|G|}\sum_g|\pi(g)v\rangle\langle\pi(g)v|=1.     \tag{7}
\]
Therefore
\[
 \begin{aligned}
 F_A(k)
 &=\frac d{|G|}\sum_g
   |\pi(kg)v\rangle\langle\pi(g)v|\\
 &=\pi(k)\frac d{|G|}\sum_g
   |\pi(g)v\rangle\langle\pi(g)v|
 =\pi(k).                                               \tag{8}
 \end{aligned}
\]
Unitary invariance of the inner product gives \(A_{sg}\pi(s)=A_g\).
After embedding the target into \(\mathbb C^d\),
\[
 B_g^*B_g=d|\pi(g)v\rangle\langle\pi(g)v|,
\]
whose eigenvalues are \(d,0,\ldots,0\). Thus
\[
 \operatorname{tr}_d|B_g^*B_g-1|
 =2\left(1-\frac1d\right),                              \tag{9}
\]
proving (GFP5)--(GFP7).

The right-translation amplification can turn this frame into exact tall
isometries. It cannot by itself turn them into unitaries on the original
carrier; that requires common-corange reduction.
