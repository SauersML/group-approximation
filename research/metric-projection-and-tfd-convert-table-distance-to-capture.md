---
rg: 2
id: metric-projection-and-tfd-convert-table-distance-to-capture
kind: route
title: Convert table distance to capture and take the metric dual
target: relative-pd-body-has-table-or-separator-dichotomy
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
  - tfd-low-leakage-compressions-flexibly-reduce
  - tfd-finite-corner-collapse-and-rfd-firewall
---

# A closest positive-definite table gives a low-leakage corner

The body in (TPD1) is nonempty: relative induction of \(\beta\) supplies a
coefficient function. It is closed and bounded in a finite-dimensional
space, hence compact and convex. Choose a minimizer \(F^\star\), and write
\[
 C_s=F^\star(s),\qquad
 \frac1{|S|}\sum_s\|U_s-C_s\|_{2,d}^2=\Delta(U)^2.        \tag{1}
\]

By **finite-positive-definite-window-is-a-relative-corner-selector**, there
are a finite-dimensional representation
\[
 \rho:G\longrightarrow U(H)
\]
and an isometry \(V:\mathbb C^d\to H\) such that
\[
 C_s=V^*\rho(s)V,\qquad
 \rho(b)V=V\beta(b)\quad(b\in B).                         \tag{2}
\]
Put \(P=VV^*\). For \(T_s=C_s\), the normalized leakage identity is
\[
 \frac1d\|(1-P)\rho(s)V\|_F^2
 =\operatorname{tr}_d(1-T_s^*T_s).                       \tag{3}
\]
Since \(U_s\) is unitary and \(T_s\) is a contraction,
\[
 \begin{aligned}
 \operatorname{tr}_d(1-T_s^*T_s)
 &\leq\|1-T_s^*T_s\|_{1,d}\\
 &\leq2\|U_s-T_s\|_{1,d}
 \leq2\|U_s-T_s\|_{2,d}.                                 \tag{4}
 \end{aligned}
\]
Average (4) and use Cauchy--Schwarz with (1). The total leakage over the
fixed set \(S\), divided by \(d\), is at most
\[
 2|S|\Delta(U).                                          \tag{5}
\]

Let \(W_s\) be a unitary polar completion of \(T_s\) on
\(\mathbb C^d\). Singular-value calculus gives
\[
 \|W_s-T_s\|_{2,d}^2
 \leq\operatorname{tr}_d(1-T_s^*T_s).                    \tag{6}
\]
Apply **tfd-low-leakage-compressions-flexibly-reduce** to \(\rho\) and
\(P\). Equations (5)--(6), followed by the triangle inequality with (1),
produce an exact representation on \(d+O(\Delta(U)d)\) dimensions at
generalized generator distance
\[
 C_A\sqrt{\Delta(U)}.                                    \tag{7}
\]
Because \(\rho\) factors through \(G\), the corrected subrepresentation and
the trivial padding also factor through \(G\). They are therefore
congruence endpoints. This proves (TPD3), uniformly in the finite quotient
and the size of the Stinespring dilation.

# Metric projection is the exact finite-dimensional separator

Give \(\bigoplus_{s\in S}M_d\) the real inner product
\[
 \langle X,Y\rangle=
 \frac1{|S|}\sum_{s\in S}
 \operatorname{Re}\operatorname{tr}_d(X_s^*Y_s).         \tag{8}
\]
Let \(C^\star\) be the metric projection of \(U\) onto the compact convex
body \(\mathcal C(G,B,\beta)\). The variational inequality for metric
projection says
\[
 \langle U-C^\star,C-C^\star\rangle\leq0
 \quad(C\in\mathcal C(G,B,\beta)).                        \tag{9}
\]
If \(\Delta(U)>0\), set
\[
 Z=(U-C^\star)/\Delta(U).
\]
Then \(\|Z\|=1\), and (9) gives
\[
 \sup_{C\in\mathcal C}\langle Z,C\rangle
 \leq\langle Z,C^\star\rangle.
\]
Therefore
\[
 \langle Z,U\rangle-\sup_{C\in\mathcal C}\langle Z,C\rangle
 \geq\langle Z,U-C^\star\rangle
 =\Delta(U),                                             \tag{10}
\]
which is (TPD4).

Finally (TPD3) implies
\[
 D(U)\geq\varepsilon
 \quad\Longrightarrow\quad
 \Delta(U)\geq(\varepsilon/C_A)^2.                       \tag{11}
\]
Use the metric separator at every coordinate and combine (10)--(11) to
obtain (TPD5) with \(c_A=C_A^{-2}\).

This separation is a complete finite-dimensional Farkas alternative for
the relative coefficient body. It does not bound the word length, matrix
rank, or quotient support of the dual witnesses as \(G\) moves. Those are
exactly the features which the bounded-moment camouflage shows cannot be
made uniform by scalar character data alone.
