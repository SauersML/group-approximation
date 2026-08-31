---
rg: 2
id: tfd-mixed-intertwiner-detects-core-character-twist
kind: route
title: Detect a nonextendible core character in the mixed intertwiner representation
target: cyclic-core-twist-forces-full-relative-cayley-cosystole
requires:
  - multi-kraus-frame-energy-is-the-full-relative-pd-gate
  - cyclic-core-character-forces-linear-rms-section-area
  - tfd-finite-corner-collapse-and-rfd-firewall
---

# Every relative coefficient table gives a mixed intertwiner vector

Fix an arbitrary relative Stinespring frame for \((G,B,\beta)\). In the
equivalent Stinespring notation, it gives a finite-dimensional
representation
\[
 \pi:G\to U(\mathscr H)
\]
and an isometry \(V:\mathbb C^d\to\mathscr H\) satisfying
\[
 \pi(b)V=V\beta(b)=\theta(b)V\rho(b)\qquad(b\in B).        \tag{1}
\]
On the Hilbert--Schmidt space
\(\operatorname{Hom}(\mathbb C^d,\mathscr H)\), define
\[
 \sigma(g)T=\pi(g)T\rho(g)^*.                             \tag{2}
\]
This is a finite-dimensional unitary representation of \(G\), and hence
of \(\Gamma\). Equation (1) gives
\[
 \sigma(b)V=\theta(b)V.                                  \tag{3}
\]

Let \(P_{\rm inv}\) be the orthogonal projection onto the invariant
subspace of \(\sigma\). Choose \(b_0\in B\) with
\(\theta(b_0)\ne1\). Since \(P_{\rm inv}\sigma(b_0)=P_{\rm inv}\),
(3) implies
\[
 P_{\rm inv}V
 =P_{\rm inv}\sigma(b_0)V
 =\theta(b_0)P_{\rm inv}V,
\]
and therefore
\[
 P_{\rm inv}V=0.                                         \tag{4}
\]
Thus the core character puts the entire Stinespring isometry in the
nontrivial part of the mixed representation; no multiplicity or target
dimension can hide it.

# The TFD gap is exactly the baseline row energy

Apply (CCT1) to \(V\), using the Hilbert--Schmidt inner product. Since
\(\|V\|_{\mathrm F}^2=d\), (4) gives
\[
 \frac1{|S|}\sum_s\frac1d
 \|\pi(s)V-V\rho(s)\|_{\mathrm F}^2\geq\gamma.             \tag{5}
\]
On the other hand, the row energy of the chosen relative frame is
\[
 \mathcal E_U^{\rm K}(A)^2
 =\frac1{|S|}\sum_s\frac1d
 \|\pi(s)V-VU_s\|_{\mathrm F}^2.                          \tag{6}
\]
Equality (6) is the Stinespring form of (MKF7); expanding the square gives
\(2-2\operatorname{Re}\operatorname{tr}_d(U_s^*F_A(s))\).

The RMS distance between the vector families in (5) and (6) is exactly
\[
 \begin{aligned}
 \left(\frac1{|S|}\sum_s\frac1d
 \|V(U_s-\rho(s))\|_{\mathrm F}^2\right)^{1/2}
 &=\left(\frac1{|S|}\sum_s|c_s-1|^2\right)^{1/2}\\
 &=h(c).                                                  \tag{7}
 \end{aligned}
\]
Minkowski in the Hilbert direct sum over \(S\) now gives
\[
 \mathcal E_U^{\rm K}(A)\geq(\sqrt\gamma-h(c))_+.          \tag{8}
\]
This holds for every relative frame and every Stinespring target, so
taking the infimum proves (CCT4). The inclusion of unitary tables in the
full frame body proves (CCT5). Finally (MKF5) gives
\[
 (\sqrt\gamma-h(c))_+
 \leq e_{\rm K}(U)
 \leq\sqrt{\Delta(U)^2+2\Delta(U)},
\]
and solving the quadratic inequality proves (CCT6).

# The Iwahori twist has vanishing rows but nonvanishing selector energy

The character in (CCT7) is the character constructed in
cyclic-core-character-forces-linear-rms-section-area. Its well-definedness
uses that the order of \(4\) modulo \(4^K-1\) is exactly \(K\): every
relation in \(B_K\) has \(r\)-exponent divisible by \(K\).

Insert (CCT8) into the square-free presentation
\[
 \langle x,r,t\mid x^2,(xr)^2,(xt)^3,\,
 rtr^{-1}t^{-4},(xt^2r)^3,t^{N_K}\rangle.
\]
All scalar phases cancel from the BS covariance row. The two words
containing \(r\) acquire respectively the scalar factors
\(\zeta_K^2\) and \(\zeta_K^3\), while every other displayed word remains
one. This proves (CCT9), and
\[
 \max\{|\zeta_K^2-1|,|\zeta_K^3-1|\}
 \leq3|\zeta_K-1|=O(K^{-1}).                             \tag{9}
\]
For the fixed marked generating set, \(h(c)=O(|\zeta_K-1|)\). Equations
(CCT4)--(CCT6) therefore give (CCT10)--(CCT11).

If \(\rho_K=\lambda_{G_K}\), then
\[
 \lambda_{G_K}|_{B_K}=[G_K:B_K]\lambda_{B_K}.
\]
Tensoring a finite-group regular representation by a character is
unitarily equivalent to itself, so \(\beta_K\) is an authenticated regular
core. The input tuple differs from the exact endpoint \(\rho_K\) only in
the \(r\)-coordinate and by exactly \(|\zeta_K-1|\). The finite reductions
separate every fixed nonidentity element along \(N_K\to\infty\), and the
extra scalar on any fixed word tends to one. Hence the family has regular
limiting character and global endpoint distance tending to zero.

The conclusion is therefore a direction check, not a refutation of the
root theorem. Fixed-core relative positive-definite distance can stay
uniformly positive while ordinary endpoint distance vanishes. Presentation
rows alone cannot distinguish those two situations. Any selector argument
which first freezes \(\beta_K\) must quotient or optimize this exact-core
motion before using curvature, expansion, or a separator.
