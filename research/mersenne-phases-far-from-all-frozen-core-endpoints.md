---
rg: 2
id: mersenne-phases-far-from-all-frozen-core-endpoints
kind: claim
title: Mersenne phases stay uniformly far from every exact endpoint over the frozen core
distinct_from:
  mersenne-phases-refute-diagonal-iwahori-decoder: that only separates the phase from diagonal exact-inversion gauges; this separates it from every exact endpoint over the unchanged regular core, with arbitrary representation type and no diagonal hypothesis.
  mersenne-phases-have-explicit-exact-core-bend: that constructs a nearby exact endpoint after moving the parabolic generator; this proves that the same phase cannot be absorbed if that generator is frozen.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that assumes equal total characters and retracts to a commutant orbit; this uses only the raw invariant-vector projection and therefore covers exact endpoints of every character.
---

**ESTABLISHED FIXED-CORE GAP; FULL STABILITY STILL OPEN.** For
\(m=4^n-1\), put

\[
 Q_n=\operatorname{SL}_2(\mathbb Z/m\mathbb Z)/\{+\!I,-I\},
 \qquad
 R_n=\lambda_{Q_n}(r),\quad T_n=\lambda_{Q_n}(t).
\]

Let \(X_{\eta,n}\) be any translated-half-interval phase endpoint from
mersenne-phases-have-explicit-exact-core-bend. Thus there is a diagonal
unitary \(U_{\eta,n}\) for which

\[
 X_{\eta,n}=U_{\eta,n}\lambda_{Q_n}(x)U_{\eta,n}^*,
 \qquad
 T_{\eta,n}=U_{\eta,n}T_nU_{\eta,n}^*,
 \qquad
 \|T_{\eta,n}-T_n\|_2^2=\frac{8}{3n}.                  \tag{FCE1}
\]

Let \(\mathcal E_n\) be the set of all unitaries \(Y\) on
\(\ell^2(Q_n)\) satisfying

\[
 Y^2=1,\qquad YR_nY=R_n^{-1},\qquad
 (YT_n)^3=1,\qquad (YT_n^2R_n)^3=1.                   \tag{FCE2}
\]

There is a constant \(\kappa_{\mathrm I}>0\), independent of \(n\), of
the translated intervals, and of \(Y\), such that every
\(Y\in\mathcal E_n\) obeys the exact alternative

\[
 \max\left\{
   \|Y-X_{\eta,n}\|_2,\,
   \sqrt{\frac{8}{3n}}
 \right\}
 \ \ge\
 \kappa_{\mathrm I}\sqrt{1-\frac1{m^2}}.               \tag{FCE3}
\]

Consequently, for all sufficiently large \(n\),

\[
 \inf_{Y\in\mathcal E_n}\|Y-X_{\eta,n}\|_2
 \ \ge\
 \kappa_{\mathrm I}\sqrt{1-\frac1{m^2}},
\]

and hence

\[
 \liminf_{n\to\infty}
 \inf_{Y\in\mathcal E_n}\|Y-X_{\eta,n}\|_2
 \ \ge\ \kappa_{\mathrm I}>0.                          \tag{FCE4}
\]

This closes the nondiagonal loophole for the **frozen** regular core:
neither a different finite-quotient character nor a nondiagonal absorber
can repair \(X_{\eta,n}\) while keeping both \(R_n\) and \(T_n\) fixed.

It does not produce a counterexample to strict or flexible
Hilbert--Schmidt stability. Equation (FCE1) and the explicit core bend give
an exact full endpoint at distance \(O(n^{-1/2})\) once \(T_n\) may move.
Thus the non-hyperlinearity root remains open.

DERIVATION
tau-core-expectation-forces-frozen-core-gap
