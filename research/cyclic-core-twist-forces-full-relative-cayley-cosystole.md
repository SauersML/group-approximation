---
rg: 2
id: cyclic-core-twist-forces-full-relative-cayley-cosystole
kind: claim
title: Cyclic core twists force a full relative Cayley cosystole
artifacts:
  - research/tfd-mixed-intertwiner-detects-core-character-twist.md
distinct_from:
  cyclic-core-character-forces-linear-rms-section-area: that proves every frozen-core word section has linear RMS filling area; this excludes every relative positive-definite, multi-Kraus, isometry, and unitary table, independently of a section.
  endpoint-conjugation-refutes-iwahori-energy: that uses a slow noncommutative endpoint conjugation to refute an inverse-Koopman estimate; this uses a scalar exact-core character and a property-(T;FD) mixed-intertwiner gap.
  cayley-expansion-aligns-isometry-frame-coranges: that identifies unitary and full Kraus energies on the expanding quotients; this proves both energies stay uniformly positive on an explicit vanishing-presentation-defect family.
---

Let \(\Gamma=\langle S\rangle\) have property \((T;FD)\), normalized so
that every finite-dimensional unitary representation \(\sigma\) and every
vector \(\xi\) orthogonal to its invariant subspace satisfy
\[
 \frac1{|S|}\sum_{s\in S}\|\sigma(s)\xi-\xi\|^2
 \geq\gamma\|\xi\|^2                                    \tag{CCT1}
\]
for one \(\gamma>0\). Let \(G\) be a finite quotient, let \(B<G\), let
\(\rho:G\to U(d)\), and let
\(\theta:B\to\mathbb T\) be a nontrivial character. Put
\[
 \beta(b)=\theta(b)\rho(b).                              \tag{CCT2}
\]
Choose phases \(c_s\in\mathbb T\) and prescribe
\[
 U_s=c_s\rho(s),\qquad
 h(c)^2=\frac1{|S|}\sum_{s\in S}|c_s-1|^2,               \tag{CCT3}
\]
with \(U_s=\beta(s)\) on the marked core generators. Then the full
relative multi-Kraus energy obeys
\[
 e_{\rm K}(U;\beta)\geq\bigl(\sqrt\gamma-h(c)\bigr)_+.     \tag{CCT4}
\]
Consequently
\[
 e_{\rm unit}(U;\beta)\geq e_{\rm K}(U;\beta),            \tag{CCT5}
\]
and the relative positive-definite distance satisfies
\[
 \Delta(U;\beta)\geq
 \sqrt{1+\bigl(\sqrt\gamma-h(c)\bigr)_+^2}-1.             \tag{CCT6}
\]
Thus the obstruction is to the complete coefficient body, not only to a
chosen word section or a flat unitary subclass.

There is an explicit Iwahori family. Put
\[
 N_K=4^K-1,\qquad G_K=A_{N_K},\qquad B_K=\langle r,t\rangle<G_K,
\]
and let
\[
 \zeta_K=e^{2\pi i/K},\qquad
 \theta_K(r)=\zeta_K,\qquad\theta_K(t)=1.                 \tag{CCT7}
\]
The character \(\theta_K\) is well defined and nontrivial. For any exact
representation \(\rho_K:G_K\to U(d_K)\), set
\[
 X_K=\rho_K(x),\qquad R_K=\zeta_K\rho_K(r),\qquad
 T_K=\rho_K(t),                                          \tag{CCT8}
\]
and authenticate the exact core
\(\beta_K=\theta_K\otimes\rho_K|_{B_K}\). Then
\[
 \begin{gathered}
 X_K^2=1,\qquad R_KT_KR_K^{-1}=T_K^4,\qquad T_K^{N_K}=1,\\
 (X_KT_K)^3=1,\qquad
 (X_KR_K)^2=\zeta_K^2 1,\qquad
 (X_KT_K^2R_K)^3=\zeta_K^3 1.                            \tag{CCT9}
 \end{gathered}
\]
Hence every square-free presentation defect tends to zero at rate
\(O(K^{-1})\), while \(h(c)=O(K^{-1})\). For all sufficiently large
\(K\),
\[
 e_{\rm K}(U_K;\beta_K)\geq\frac{\sqrt\gamma}{2},\qquad
 e_{\rm unit}(U_K;\beta_K)\geq\frac{\sqrt\gamma}{2},      \tag{CCT10}
\]
and
\[
 \Delta(U_K;\beta_K)\geq\sqrt{1+\gamma/4}-1.              \tag{CCT11}
\]

Taking \(\rho_K=\lambda_{G_K}\) puts the example on the regular face.
The twisted core is unitarily equivalent to the untwisted regular core,
and the marked tuple is at generator distance at most
\(|\zeta_K-1|\) from the exact endpoint \(\rho_K\). Its fixed-word
characters converge to the regular character. Therefore this is not a
counterexample to Dogon--Vigdorovich repair: moving the core removes it at
cost \(O(K^{-1})\). It is an exact counterexample to every implication
\[
 \text{vanishing Iwahori presentation defect}
 \Longrightarrow e_{\rm unit}\to0
 \quad\text{or}\quad e_{\rm K}\to0                       \tag{CCT12}
\]
which freezes the authenticated coordinate core.

Accordingly a spanning-tree gauge, expander filling, or nonlinear
Poincare theorem cannot close the fixed-core arrow from the cubic rows.
A viable positive-definite selector must first minimize over nearby exact
core coordinates, as in gauge-optimized-induced-energy-target, or use an
additional hypothesis extracted from a genuine positive-distance capture
enemy. The root problem remains open.

DERIVATION
tfd-mixed-intertwiner-detects-core-character-twist
