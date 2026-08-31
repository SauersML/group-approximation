---
rg: 2
id: stinespring-leakage-and-word-fillings-audit-ulam-input
kind: route
title: Audit Ulam input by Stinespring leakage and presentation filling areas
target: alekseev-thom-starts-after-full-iwahori-leakage
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
  - induced-rounding-needs-rms-section-fillings
---

# The cited theorem has a uniform unit-ball hypothesis

Definition 2.1 of arXiv:2606.07369v1 requires, for all contractions
\(x,y\), with the usual restriction that \(x+y\) is again a contraction,
and every \(|\lambda|\leq1\),
\[
 \begin{aligned}
 \|\varphi(x+y)-\varphi(x)-\varphi(y)\|_2&\leq\varepsilon,\\
 \|\varphi(\lambda x)-\lambda\varphi(x)\|_2&\leq\varepsilon,\\
 \|\varphi(xy)-\varphi(x)\varphi(y)\|_2&\leq\varepsilon,\\
 \|\varphi(x^*)-\varphi(x)^*\|_2&\leq\varepsilon,\\
 \|\varphi(1)-1\|_2&\leq\varepsilon.                     \tag{1}
 \end{aligned}
\]
Theorem 3.5 supplies a modulus independent of the matrix size, but assumes
all of (1). It embeds the target as a trace-one corner \(pPp\), produces a
finite corner \(qPq\), and a unital star-homomorphism
\(\psi:M_n(\mathbb C)\to qPq\) satisfying
\[
 \sup_{\|x\|\leq1}\|\varphi(x)-\psi(x)\|_2
 \leq\omega(\varepsilon),\qquad\omega(\varepsilon)\to0. \tag{2}
\]
There is no trace-preservation hypothesis in (1); approximate trace
preservation is derived in their proof. There is also no theorem there
whose input is a finite list of group relators.

# Compression multiplicativity is the missing off-corner estimate

Let \(\pi:M_n(\mathbb C)\to B(\mathscr K)\) be a star-representation and
let \(V\) be an isometry into \(\mathscr K\). Put \(P=VV^*\). Direct
multiplication gives
\[
 \begin{aligned}
 V^*\pi(xy)V-V^*\pi(x)VV^*\pi(y)V
 &=V^*\pi(x)(1-P)\pi(y)V.                                \tag{3}
 \end{aligned}
\]
Additivity, homogeneity, star preservation, and unitality of this
compression are exact. From (3),
\[
 \sup_{\|x\|,\|y\|\leq1}
 \|\varphi(xy)-\varphi(x)\varphi(y)\|_2
 \leq
 \sup_{\|y\|\leq1}\|(1-P)\pi(y)V\|_2.                    \tag{4}
\]
The right side is a uniform leakage over the full unit ball. In a regular
Stinespring realization it includes every matrix-unit row, whereas (MKF4)
averages only the fixed marked Iwahori rows. Proving (4) tends to zero from
the two cubics would therefore be a new all-row theorem stronger than the
current positive-definite gate. The Ulam theorem can consume (4); it
cannot prove (4) from the cubics.

# Finite presentation estimates retain the moving filling constant

Let
\[
 \Gamma=\langle S\mid\mathcal R\rangle
\]
be a finite presentation and let \(U_s\) be unitaries with
\[
 \max_{r\in\mathcal R}\|U_r-1\|_2\leq\delta.             \tag{5}
\]
If a null word \(w\) is a product of \(A\) conjugates of relators or their
inverses, bi-invariance of normalized Hilbert--Schmidt norm and telescoping
give
\[
 \|U_w-1\|_2\leq A\delta.                                \tag{6}
\]
Now let \(G\) be a finite quotient and choose word representatives
\(\sigma(g)\). If
\[
 A(g,h)=\operatorname{Area}_{\mathcal R}
 \left(\sigma(g)\sigma(h)\sigma(gh)^{-1}\right),         \tag{7}
\]
then the basis assignment
\(\Phi(\lambda_g)=U_{\sigma(g)}\) satisfies
\[
 \|\Phi(\lambda_g)\Phi(\lambda_h)-\Phi(\lambda_{gh})\|_2
 \leq A(g,h)\delta.                                      \tag{8}
\]
Suppose, as an extra hypothesis not supplied by (5), that the linear
extension sends contractions to contractions. For
\(x=\sum_ga_g\lambda_g\) and \(y=\sum_hb_h\lambda_h\), (8) gives
\[
 \|\Phi(x)\Phi(y)-\Phi(xy)\|_2
 \leq A_{\max}\delta
       \left(\sum_g|a_g|\right)\left(\sum_h|b_h|\right). \tag{9}
\]
The canonical trace on the regular group algebra gives
\(\sum_g|a_g|^2=\|x\|_2^2\leq\|x\|^2\leq1\), and similarly
for \(y\). Hence each first norm is at most \(|G|^{1/2}\), proving
\[
 \|\Phi(x)\Phi(y)-\Phi(xy)\|_2
 \leq |G|A_{\max}\delta.                                \tag{10}
\]
This is only a sufficient crude estimate, not a claimed optimal constant.
Its role is exact: finite presentation control keeps a moving filling and
coefficient-summation loss. A dimension-free cancellation, completely
positive construction, or nonlinear synchronization theorem could improve
(10), but none is contained in the relator telescope or in
Alekseev--Thom.

If a future construction supplies maps satisfying (1), matches their
marked quotient unitaries to the Iwahori tuple, and has
\(\varepsilon\to0\), (2) becomes a legitimate amplified endpoint repair.
Until then the matrix-algebra theorem lies after, rather than before, the
full leakage gate.
