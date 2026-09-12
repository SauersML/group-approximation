---
rg: 2
id: p13-hodge-robust-rotation-gap
kind: claim
title: The literal P13 Hodge certificate has an explicit robust rotation modulus
distinct_from:
  p13-rotation-relator-defect-219: That claim controls the thirteen substituted relators; this claim propagates their individual costs through every Hodge support-product replay and the Fox chain.
  literal-base-explicit-kazhdan-pair: That is an honest-representation Kazhdan pair for the full affine base; this is a defective-tuple spectral estimate for the six substituted rotation words.
  effective-transport-modulus: This closes the P13 rotation stage only; robust affine relative-T control and the downstream transport ledger remain.
artifacts:
  - GroupApproximation/Sofic/LiteralP13HodgeData.lean
  - GroupApproximation/Sofic/LiteralP13HodgeReplay.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificateCore.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationReplay.lean
---

Let \(X,Y,Z\) be unitaries for which each of the eight literal rotation
relators has operator-norm defect at most \(\delta\). Substitute the six P13
words from `p13-rotation-relator-defect-219`, write the resulting unitaries
as \(U_0,\ldots,U_5\), and set

\[
\Delta_U=\sum_{i=0}^5(2I-U_i-U_i^*).
\]

Then every vector \(\xi\) satisfies the robust quadratic Hodge estimate

\[
\left(\gamma-6692\delta-599314\delta^2\right)
  \langle \xi,\Delta_U\xi\rangle
\leq
  \|\Delta_U\xi\|^2+196350\delta^2\|\xi\|^2,
\qquad
\gamma=\frac{28329113480286}{10^{16}}.
\tag{1}
\]

The constant \(\gamma\), slightly stronger than the public \(1/500\), is the
exact certificate gap

\[
\frac1{250}-\frac{11670886519714}{10^{16}}
 =\frac{28329113480286}{10^{16}}.
\]

Consequently, put

\[
a_\delta=\gamma-6692\delta-599314\delta^2.
\]

If

\[
0\leq\delta<\delta_{\rm P13},
\]

where \(\delta_{\rm P13}\) is the positive root of

\[
599314\delta^2+
(6692+2\sqrt{196350})\delta-\gamma=0,
\]

then

\[
\delta_{\rm P13}=3.7381134709\ldots\times10^{-7}
\]

and, with

\[
\lambda_\pm(\delta)=
\frac{a_\delta\pm\sqrt{a_\delta^2-4\cdot196350\delta^2}}2,
\]

one has

\[
\operatorname{spec}(\Delta_U)
\subseteq [0,\lambda_-(\delta)]\cup
[\lambda_+(\delta),\infty).
\tag{2}
\]

Thus the finite P13 replay aggregation is no longer a missing modulus. This
does not yet yield `effective-transport-modulus`: the exact affine bridge
uses rotation conjugators of unbounded word length, and (2) supplies a low
spectral cluster rather than an exactly rotation-fixed subspace.
