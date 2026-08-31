---
rg: 2
id: almost-full-hecke-frame-gives-flexible-corner
kind: claim
title: An almost-full near-top Hecke frame gives the flexible finite corner
distinct_from:
  hecke-top-spectrum-coverage-controls-window: that treats an exactly unital near-top frame; this permits a missing trace carrier and pays it at the flexible rank scale.
  tfd-low-leakage-compressions-flexibly-reduce: that rounds a low-leakage projection after a finite representation is given; this constructs the finite relative corner from a partially covering Hecke frame.
  tfd-finite-corner-collapse-and-rfd-firewall: that permits arbitrary ambient dilation dimension; this quantifies a finite induced-space certificate which produces such a dilation.
---

Retain the regular finite-core notation and let

\[
{\cal H}_\epsilon
 =1_{[1-\epsilon,1]}(T_X)L^2(D).
\]

Suppose there are finitely many \(A_j\in{\cal H}_\epsilon\) for which

\[
P=\sum_jA_j^*A_j\leq1,\qquad
\tau(1-P)\leq\delta.                                   \tag{AHF1}
\]

Then

\[
\Delta^{\rm reg}_{G,B}(X)
 \leq\sqrt{2\epsilon+4\delta}.                         \tag{AHF2}
\]

In particular, a moving regular Iwahori sequence has finite relative
corners whenever there are \(\epsilon_n,\delta_n\to0\) and near-top
Hecke frames satisfying (AHF1).  Property \((T;FD)\) then gives exact
endpoints on \(d_n+o(d_n)\) dimensions.

To prove the estimate, add the filler

\[
A_0=(1-P)^{1/2}\in D.
\]

Now \(\sum_{j\geq0}A_j^*A_j=1\), so these operators define a relative
Kraus window.  For the near-top columns, spectral calculus gives

\[
\sum_{j\geq1}\|X_0A_j-A_jX\|_2^2
 =2\sum_{j\geq1}\langle A_j,(1-T_X)A_j\rangle
 \leq2\epsilon\,\tau(P)\leq2\epsilon.                 \tag{AHF3}
\]

The filler has

\[
\|X_0A_0-A_0X\|_2
 \leq2\|A_0\|_2,
\qquad
\|A_0\|_2^2=\tau(1-P)\leq\delta.                       \tag{AHF4}
\]

Let \(C=\sum_{j\geq0}A_j^*X_0A_j\).  As before,

\[
C-X=\sum_{j\geq0}A_j^*(X_0A_j-A_jX).
\]

The Kraus row is a coisometry, so its product with the error column has
Hilbert--Schmidt norm at most the column norm.  Equations (AHF3)--(AHF4)
give (AHF2).

The criterion is deliberately trace-flexible.  It does not require the
near-top space to cover a small exceptional carrier or require that carrier
to be invariant under the core or the supplied involution; the square-root
filler absorbs it inside the finite Stinespring corner.  Thus a genuine
negative sequence must prevent **almost-full contractive coverage**, not
merely exact frame coverage.  No current arithmetic estimate decides this
for the moving \(A_N,B_N\) Hecke modules, so the root remains open.

DERIVATION
almost-full-hecke-frame-corner-proof
