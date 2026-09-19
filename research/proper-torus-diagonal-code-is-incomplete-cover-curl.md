---
rg: 2
id: proper-torus-diagonal-code-is-incomplete-cover-curl
kind: claim
title: Proper-torus diagonal parity is curl on an incomplete gain-cover complex
distinct_from:
  diagonal-exact-inversion-is-two-cubic-parity-code: that gives the parity-check matrix on normalizer-invariant group functions; this constructs its intrinsic vertex-edge-triangle complex.
  proper-torus-reynolds-is-edge-refinement: that analyzes the real signed Green operator and proves infinity-norm divergence; this identifies the mod-two cohomology and Hamming-decoding complex for diagonal involution gauges.
  full-torus-diagonal-parity-has-linear-decoder: that solves the base complete-graph complex by a vertex anchor; this isolates precisely how a proper torus changes the one-skeleton and omits triangle lifts.
---

Let \(G=\operatorname{PSL}_2(\mathbb F_p)\), let \(T_s\) be its full
projective split torus, and put
\[
 H=\langle h(2)\rangle,\quad i=[T_s:H],\quad
 U=\langle t\rangle,\quad P=UH,
\]
\[
 N=\langle H,x\rangle,\quad
 \overline P=UT_s,\quad \overline N=\langle T_s,x\rangle.
\]
There is a canonical graph \(Z_H\) with
\[
 V(Z_H)=P\backslash G,\qquad E(Z_H)=N\backslash G,      \tag{IGC1}
\]
where the edge \(Ng\) has endpoints
\[
 Pg\quad\hbox{and}\quad Pxg.                            \tag{IGC2}
\]
The maps induced by \(P<\overline P\) and
\(N<\overline N\) make
\[
 Z_H\longrightarrow K_{p+1}                            \tag{IGC3}
\]
an \(i\)-sheeted graph covering. In particular,
\[
 |V(Z_H)|=i(p+1),\qquad
 |E(Z_H)|=i\binom{p+1}{2}.                              \tag{IGC4}
\]

Put \(a=xt\) and \(b=xt^2r\). Each row in
\[
 \langle a\rangle\backslash G
 \quad\hbox{or}\quad
 \langle b\rangle\backslash G
\]
selects the three edges of a 3-cycle in \(Z_H\). Attach one 2-cell along
every selected 3-cycle and call the resulting complex \(K_H\). Over
\(\mathbb F_2\), its cellular curl is exactly the diagonal cubic syndrome:
\[
 \delta_1:C^1(K_H;\mathbb F_2)\longrightarrow
 C^2(K_H;\mathbb F_2),\qquad
 \delta_1c=(h_a(c),h_b(c)).                             \tag{IGC5}
\]
Consequently
\[
 {\cal C}_N=Z^1(K_H;\mathbb F_2),                       \tag{IGC6}
\]
and the vertex-gauge subcode is
\[
 B^1(K_H;\mathbb F_2)
 =\{c(Ng)=\phi(Pg)+\phi(Pxg)\}.                         \tag{IGC7}
\]
Thus
\[
 {\cal C}_N/B^1(K_H;\mathbb F_2)
 \cong H^1(K_H;\mathbb F_2)                             \tag{IGC8}
\]
is the exact finite obstruction to saying that every flat diagonal gauge
is a vertex cut.

Although (IGC3) is a genuine covering of graphs, \(K_H\) is not the
\(i\)-sheeted simplicial cover of the full-torus triangle complex when
\(i>1\). The two triangle row sets are independent of \(H\): each base
cyclic triangle receives one correlated lift rather than all \(i\) deck
translates. This is the incomplete-label phenomenon in a precise cellular
form.

The diagonal trace-Cheeger problem is therefore the binary coboundary
soundness of the explicit complexes \(K_H\):
\[
 \operatorname{dist}(c,Z^1(K_H))
 \leq\omega\!\left(
 \frac{|\operatorname{supp}\delta_1c|}{|G|}\right),
 \qquad\omega(s)\to0.                                  \tag{IGC9}
\]
Real infinity-norm Green divergence does not decide (IGC9), and neither
vanishing nor nonvanishing of (IGC8) alone decides it. The general
proper-torus decoder and the non-hyperlinearity root remain open.

DERIVATION
proper-torus-incomplete-cover-curl-proof
