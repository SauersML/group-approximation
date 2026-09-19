---
rg: 2
id: amplify-right-translates-and-preserve-frame-energy
kind: route
title: Amplify over right translates while preserving coefficients and row energy
target: right-translation-flattens-every-relative-kraus-frame
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
---

# Every translated fibre has normalized Gram one

From (RTF1),
\[
 \widetilde A_g^*\widetilde A_g
 =\frac1{|G|}\sum_{h\in G}A_{gh}^*A_{gh}
 =\frac1{|G|}\sum_{q\in G}A_q^*A_q
 =\frac1{|G|}1,                                         \tag{1}
\]
because right multiplication by \(g\) permutes \(G\). This proves
(RTF2). The original relative identity gives, component by component,
\[
 A_{bgh}=A_{gh}\beta(b)^*,
\]
which proves (RTF3). Summing (1) over \(g\) also verifies that
\(\widetilde A\) remains a normalized Stinespring frame.

# Right translation preserves every coefficient

For \(k\in G\),
\[
 \begin{aligned}
 F_{\widetilde A}(k)
 &=\sum_g\widetilde A_{kg}^*\widetilde A_g\\
 &=\frac1{|G|}\sum_{g,h}A_{kgh}^*A_{gh}\\
 &=\frac1{|G|}\sum_h\sum_{q\in G}A_{kq}^*A_q
 =F_A(k).                                               \tag{2}
 \end{aligned}
\]
Here \(q=gh\) for each fixed \(h\). Thus the operation preserves the
entire positive-definite function, not only the marked coordinates.

# The same reindexing preserves row energy

For every \(s\in S\),
\[
 \begin{aligned}
 \sum_g\|\widetilde A_{sg}U_s-\widetilde A_g\|_{2,d}^2
 &=\frac1{|G|}\sum_{g,h}
   \|A_{sgh}U_s-A_{gh}\|_{2,d}^2\\
 &=\sum_{q\in G}\|A_{sq}U_s-A_q\|_{2,d}^2.              \tag{3}
 \end{aligned}
\]
Averaging (3) over \(s\) proves the energy identity in (RTF4).

Set \(V_g=|G|^{1/2}\widetilde A_g\). Equation (1) says \(V_g^*V_g=1\);
(2)--(3) become (RTF5) and the energy in (RTF7). Conversely, any isometry
family satisfying (RTF6) gives a relative frame
\[
 A_g=|G|^{-1/2}V_g.
\]
Its normalization, coefficient function, and energy are exactly the
displayed formulas. This proves equality of the two infima in (RTF7).
Combining it with (MKF5) proves (RTF8).

When \(R=d\), every isometry \(V_g:\mathbb C^d\to\mathbb C^d\) is unitary
and \(W_g=V_g^*\) has the relative equivariance in (RCO2). For \(R>d\),
fibrewise polar decomposition changes nothing because the fibres are
already isometries. The required operation is to align the range
projections \(V_gV_g^*\) with one common \(d\)-plane.
Cayley-expansion-aligns-isometry-frame-coranges performs exactly that
operation with constant \(1+2\sqrt{2/\gamma}\) whenever the finite
quotient Cayley graph has Poincare gap \(\gamma\). Property \((T;FD)\)
makes this constant uniform for the authenticated quotients.
