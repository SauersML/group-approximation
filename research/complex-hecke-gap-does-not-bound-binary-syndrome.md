---
rg: 2
id: complex-hecke-gap-does-not-bound-binary-syndrome
kind: claim
title: A complex Hecke gap needs an integral filling theorem before it controls binary soundness
distinct_from:
  diagonal-parity-is-hecke-but-tau-misses-local-links: that separates the global automorphic gap from a collapsing real link gap; this gives the exact characteristic-zero versus mod-two conversion fence even if a complex singular gap were available.
  binary-cubic-curl-has-global-torus-hecke-blocks: that block-diagonalizes the characteristic-two incidence map; this explains why complex singular values of formally similar blocks do not yield Hamming decoding.
  proper-torus-reynolds-is-edge-refinement: that proves an infinity-norm real inverse diverges; this distinguishes every real filling norm from the required mod-two support filling norm.
---

Let \(D:\mathbb Z^E\to\mathbb Z^F\) be any integral incidence matrix and
let \(\overline D\) be its reduction modulo two. For a binary syndrome
\(h\in\operatorname{ran}\overline D\), define its mod-two filling norm
\[
 \operatorname{Fill}_2(h)
 =\min\{|\operatorname{supp}e|:
        e\in\mathbb F_2^E,\ \overline De=h\}.           \tag{CGF1}
\]
For every binary cochain \(c\),
\[
 \operatorname{dist}_{\rm Ham}
       (c,\ker\overline D)
 =\operatorname{Fill}_2(\overline Dc).                 \tag{CGF2}
\]
Thus a uniform Hamming decoder is exactly a uniform support estimate for
(CGf1), after normalization by \(E\) and \(F\).

A positive smallest nonzero singular value of
\(D_{\mathbb C}\) controls instead the real Hilbert filling problem
\[
 \inf\{\|v\|_2:D_{\mathbb C}v=y\}
 \leq\sigma_{\min}^+(D_{\mathbb C})^{-1}\|y\|_2         \tag{CGF3}
\]
for \(y\) in the complex range. There is no formal passage from (CGF3)
to (CGF1). If \(\widetilde c\in\{0,1\}^E\) and
\(\widetilde h\in\{0,1\}^F\) are the standard lifts, then only
\[
 D\widetilde c=2q+\widetilde h,\qquad q\in\mathbb Z^F, \tag{CGF4}
\]
is forced. The even charge \(2q\) is invisible to the binary syndrome
but is fully visible to every characteristic-zero singular value.

This mismatch occurs already for one three-term incidence row:
\[
 D_0=\begin{bmatrix}1&1&1\end{bmatrix},\qquad
 c_0=(1,1,0)^T.                                        \tag{CGF5}
\]
One has
\[
 \overline D_0c_0=0,\qquad D_0\widetilde c_0=2,
 \qquad \sigma_{\min}^+(D_0)=\sqrt3.                   \tag{CGF6}
\]
Direct sums of (CGF5) retain the same uniform nonzero singular value
while producing arbitrarily many independent zero-syndrome binary
vectors whose standard lifts carry nonzero even charge.

For the proper-torus diagonal complex, the integral two-cubic matrix
\[
 D=(1+L_a+L_a^2,\ 1+L_b+L_b^2)
\]
has precisely this three-term form row by row. Its complex Hecke normal
operator and its modular reduction are both exact and useful, but a
uniform complex gap would bound only (CGF3). To obtain diagonal
trace-Cheeger soundness one must additionally prove the genuine
arithmetic filling estimate
\[
 \frac{\operatorname{Fill}_2(h)}{|E|}
 \leq\omega\!\left(\frac{|\operatorname{supp}h|}{|F|}\right),
 \qquad\omega(s)\to0,                                  \tag{CGF7}
\]
uniformly over the congruence family. Neither property tau nor blockwise
complex singular values supply (CGF7). No failure of (CGF7) is asserted,
so the root remains open.

DERIVATION
complex-gap-binary-filling-fence-proof
