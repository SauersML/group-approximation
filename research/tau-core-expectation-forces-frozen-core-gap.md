---
rg: 2
id: tau-core-expectation-forces-frozen-core-gap
kind: route
title: Combine the congruence intertwiner gap with the exact parabolic conditional expectation
target: mersenne-phases-far-from-all-frozen-core-endpoints
requires:
  - iwahori-square-free-bs14-presentation
  - odd-principal-kernel-is-one-root-normal-closure
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - mersenne-phases-have-explicit-exact-core-bend
---

Fix \(n\), write \(Q=Q_n\), \(m=4^n-1\), and abbreviate

\[
 \lambda=\lambda_Q,\qquad
 U=U_{\eta,n},\qquad
 X_\eta=U\lambda(x)U^*,\qquad
 T_\eta=U\lambda(t)U^*.
\]

Let \(Y\in\mathcal E_n\). The square-free presentation defines an exact
representation

\[
 \rho:\Gamma=\operatorname{PSL}_2(\mathbb Z[1/2])
       \longrightarrow U(\ell^2Q)
\]

by

\[
 \rho(x)=Y,\qquad \rho(r)=\lambda(r),\qquad
 \rho(t)=\lambda(t).                                    \tag{TCE1}
\]

Because \(\lambda(t)^m=1\), the kernel of \(\rho\) contains the normal
closure of \(t^m\). The odd-level Mennicke theorem identifies this normal
closure with the projective level-\(m\) kernel. Hence \(\rho\) factors
through \(Q\). The conjugated regular representation

\[
 \sigma=\operatorname{Ad}(U)\circ\lambda
\]

also factors through \(Q\), and

\[
 \sigma(x)=X_\eta,\qquad \sigma(t)=T_\eta.               \tag{TCE2}
\]

We use normalized Hilbert--Schmidt norm on
\(\operatorname{End}(\ell^2Q)\). Selberg property \((\tau)\), in the
fixed standard modular generators \(x,t\), supplies a number
\(\kappa_{\mathrm I}>0\), independent of the odd congruence quotient,
such that every congruence representation has

\[
 \max_{s\in\{x,t\}}\|\Pi(s)v-v\|_2
 \ge \kappa_{\mathrm I}\|v\|_2                          \tag{TCE3}
\]

on the orthogonal complement of its invariant vectors. This is the
invariant-vector estimate isolated in
sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair. Equivalently one may
transfer its fixed generating set to \(x,t\); the finite word-length loss
is absorbed once and for all into \(\kappa_{\mathrm I}\).

Apply (TCE3) to the left-right representation

\[
 \Pi(g)A=\rho(g)A\sigma(g)^*
\]

on normalized Hilbert--Schmidt matrices. Let \(A_0\) be the orthogonal
projection of \(I\) onto \(\operatorname{Fix}(\Pi)\), and put

\[
 \delta=\max\{\|Y-X_\eta\|_2,\ \|T-T_\eta\|_2\}.         \tag{TCE4}
\]

Since \(\Pi(s)A_0=A_0\), applying (TCE3) to \(I-A_0\) gives

\[
 \|I-A_0\|_2\le\frac{\delta}{\kappa_{\mathrm I}}.        \tag{TCE5}
\]

No equality of characters is used here, and \(A_0\) is not polar-completed.

Now put \(P=\langle r,t\rangle<Q\) and
\(\mathcal M=\lambda(P)'\). For every \(p\in P\), equations
(TCE1)--(TCE2) and the exact intertwining identity for \(A_0\) give

\[
 \lambda(p)A_0=A_0U\lambda(p)U^*,
 \qquad
 \lambda(p)A_0U=A_0U\lambda(p).                         \tag{TCE6}
\]

Thus \(A_0U\in\mathcal M\).

It remains to compute the distance of \(U\) from \(\mathcal M\). The
orthogonal conditional expectation is

\[
 E_{\mathcal M}(Z)=\frac1{|P|}
   \sum_{p\in P}\lambda(p)Z\lambda(p)^*.                \tag{TCE7}
\]

On every left \(P\)-orbit, the diagonal sign defining \(U\) equals
\(-1\) on \((m-1)/2\) of the \(m\) half-edge labels and \(+1\) on the
remaining \((m+1)/2\) labels. Each label occurs \(|H|=2n\) times among
the group coordinates, including the corrected central-sign
multiplicity. Therefore its orbit average is exactly

\[
 \frac{(m+1)/2-(m-1)/2}{m}=\frac1m,
\]

independently of the translated interval at that vertex. Hence

\[
 E_{\mathcal M}(U)=\frac1m I,\qquad
 \operatorname{dist}_2(U,\mathcal M)
 =\sqrt{\|U\|_2^2-\|E_{\mathcal M}(U)\|_2^2}
 =\sqrt{1-\frac1{m^2}}.                                 \tag{TCE8}
\]

Because \(A_0U\in\mathcal M\), equations (TCE5) and (TCE8) imply

\[
 \sqrt{1-\frac1{m^2}}
 \le \|U-A_0U\|_2
 =\|I-A_0\|_2
 \le \frac{\delta}{\kappa_{\mathrm I}}.                 \tag{TCE9}
\]

Finally the exact core-bend count gives

\[
 \|T-T_\eta\|_2=\sqrt{\frac{8}{3n}}.                    \tag{TCE10}
\]

Substitution of (TCE10) into (TCE4)--(TCE9) proves (FCE3).
For sufficiently large \(n\), the second entry of the maximum in (FCE3)
is smaller than its right-hand side, so the first entry satisfies the
same lower bound. This proves (FCE4).

The argument deliberately stops at the frozen-core boundary:
\(U\) itself conjugates the regular endpoint to the exact nearby tuple
\((X_\eta,R,T_\eta)\), so no analogous lower bound can hold when the
parabolic coordinate is allowed its \(O(n^{-1/2})\) motion.
