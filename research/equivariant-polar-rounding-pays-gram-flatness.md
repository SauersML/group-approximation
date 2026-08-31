---
rg: 2
id: equivariant-polar-rounding-pays-gram-flatness
kind: route
title: Polar-round each relative fibre and pay exactly its Gram defect
target: gram-flat-kraus-frames-polarize-to-unitary-tables
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
---

# Equivariant polar choices

For each representative \(g\) of a left \(B\)-coset, take a polar
decomposition
\[
 B_g=Q_g|B_g|
\]
and extend the polar partial isometry to a unitary \(Q_g\in U(d)\). Since
the matrices are square, the kernel and cokernel have equal dimension, so
such an extension exists. Define on the rest of the coset
\[
 Q_{bg}=Q_g\beta(b)^*.                                   \tag{1}
\]
The frame relation \(B_{bg}=B_g\beta(b)^*\) shows that (1) is a unitary
polar extension for \(B_{bg}\) as well. Put
\[
 W_g=Q_g^*.                                              \tag{2}
\]
Then \(W_{bg}=\beta(b)W_g\), proving (GFP2).

For every positive scalar \(t\),
\[
 (\sqrt t-1)^2\leq|t-1|.
\]
Functional calculus therefore gives
\[
 \|B_g-Q_g\|_{2,d}^2
 =\operatorname{tr}_d(|B_g|-1)^2
 \leq\operatorname{tr}_d|B_g^*B_g-1|.                   \tag{3}
\]
Consequently
\[
 \left(\frac1{|G|}\sum_g\|B_g-Q_g\|_{2,d}^2\right)^{1/2}
 \leq\sqrt{\eta_{\rm gr}(A)}.                           \tag{4}
\]

# The row energy pays two polar errors

Bi-invariance of normalized Hilbert--Schmidt norm gives
\[
 \|U_sW_g-W_{sg}\|_{2,d}
 =\|Q_{sg}U_s-Q_g\|_{2,d}.                              \tag{5}
\]
Also, by \(B_g=|G|^{1/2}A_g\),
\[
 \mathcal E_U^{\rm K}(A)^2
 =\frac1{|S||G|}\sum_{s,g}
   \|B_{sg}U_s-B_g\|_{2,d}^2.                            \tag{6}
\]
For each edge,
\[
 \begin{aligned}
 \|Q_{sg}U_s-Q_g\|_{2,d}
 &\leq\|B_{sg}U_s-B_g\|_{2,d}\\
 &\quad+\|Q_{sg}-B_{sg}\|_{2,d}
       +\|Q_g-B_g\|_{2,d}.                              \tag{7}
 \end{aligned}
\]
Minkowski's inequality in the Hilbert direct sum over \(S\times G\),
followed by (4) for each of the last two terms, proves (GFP3).

# A zero-energy frame need not be flat

For (GFP4), Schur orthogonality gives
\[
 \frac d{|G|}\sum_g|\pi(g)v\rangle\langle\pi(g)v|=1,     \tag{8}
\]
which is the frame normalization. Moreover,
\[
 \begin{aligned}
 F_A(k)
 &=\frac d{|G|}\sum_g
   |\pi(kg)v\rangle\langle\pi(g)v|\\
 &=\pi(k)\frac d{|G|}\sum_g
   |\pi(g)v\rangle\langle\pi(g)v|
 =\pi(k),                                               \tag{9}
 \end{aligned}
\]
and unitary invariance of the inner product proves \(A_{sg}\pi(s)=A_g\).
This proves (GFP5)--(GFP6).

After a fixed isometric embedding \(\mathbb C\hookrightarrow\mathbb C^d\),
\(B_g^*B_g=d|\pi(g)v\rangle\langle\pi(g)v|\). Its eigenvalues are \(d\)
once and zero \(d-1\) times, so
\[
 \operatorname{tr}_d|B_g^*B_g-1|
 =\frac{(d-1)+(d-1)}d
 =2\left(1-\frac1d\right),                              \tag{10}
\]
proving (GFP7). Thus energy minimization and pointwise polar flattening are
separate operations even at an exact endpoint.
