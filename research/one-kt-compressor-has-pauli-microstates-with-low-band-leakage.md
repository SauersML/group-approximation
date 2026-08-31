---
rg: 2
id: one-kt-compressor-has-pauli-microstates-with-low-band-leakage
kind: claim
title: One Kun--Thom compressor has marked Pauli microstates with maximal low-band leakage
artifacts:
  - research/one-kt-compressor-pauli-low-band-countermodel-proof.md
distinct_from:
  strict-compressor-mixed-return-collapses-shared-pauli-sign: that proves collapse for genuine finite-dimensional actors and isolates compressor low-band normalization; this gives a Pauli-compatible countermodel to that normalization for one actual Kun--Thom compressor.
  kt-nested-compressor-flat-tower-has-uniform-wall: that constructs an explicit two-fold relative wall for the one-compressor actor; this realizes the whole shared-center Pauli presentation and keeps the central sign maximally separated.
  monomial-ascending-hnn-coset-action-sofic: that proves the underlying coset action is sofic; this applies the marked common-center Pauli chart theorem and quantifies the resulting operator-norm low-band leakage.
  kt-two-positive-compressors-generate-full-obstruction: that proves two positive compressors already generate the full nons​​ofic action; this proves one compressor is insufficient even after naming both Pauli coordinates.
---

**ESTABLISHED PAULI-COMPATIBLE COUNTERMODEL FOR EVERY ONE-COMPRESSOR
SLICE; THE FULL KUN--THOM ACTOR REMAINS OPEN.**

Use the Kun--Thom polynomial vertex
\[
 \Gamma=\operatorname{EL}_r(\mathbb F_q[x_1,\ldots,x_d]),
 \qquad r,d\geq3,
\]
and a positive monomial matrix \(T\in\operatorname{SL}_d(\mathbb Z)\)
such that
\[
 \alpha(\Gamma)=T\Gamma T^{-1}<\Gamma.
\]
Put
\[
 V_T=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma)
       \ (\gamma\in\Gamma)\rangle,\qquad X=V_T/\Gamma.    \tag{KPL1}
\]
Then \(\Gamma\) is an infinite Kazhdan point stabilizer and \(t\) is a
strict compressor.

Let \(P_X\) be the shared-center Pauli group on \(X\), with root
generators \(A_x,B_x\) and common central involution \(J\), and put
\[
             \Pi_T=P_X\rtimes V_T.                       \tag{KPL2}
\]
Then
\[
             \boxed{\ \Pi_T\text{ is sofic.}\ }           \tag{KPL3}
\]
Moreover it has canonical sofic, hence normalized-Hilbert--Schmidt,
microstates in which
\[
             \|J-I\|_2\longrightarrow\sqrt2.             \tag{KPL4}
\]

Choose
\[
 \gamma_0\in\Gamma\setminus\alpha(\Gamma),\qquad
 r_0=t^{-1}\gamma_0t\notin\Gamma.                         \tag{KPL5}
\]
Writing \(o=\Gamma\in X\), the same microstates satisfy
\[
\begin{aligned}
 \max_{q\in Q}\|[B_o,u_q]\|_2&\longrightarrow0,\\
 \|[A_o,u_{r_0}B_ou_{r_0}^*]\|_2&\longrightarrow0,\\
 \|u_{r_0}B_ou_{r_0}^*-B_o\|_2&\longrightarrow\sqrt2,     \tag{KPL6}
\end{aligned}
\]
for every fixed Kazhdan generating set \(Q\) of \(\Gamma\).
Thus the mixed-return normalization implication
\[
 B\text{ is asymptotically }\Gamma\text{-central}
 \quad\Longrightarrow\quad
 u_{r_0}Bu_{r_0}^*-B\longrightarrow0                    \tag{KPL7}
\]
is false for the one-compressor Kun--Thom actor, even on microstates which
extend across the entire shared-Pauli group.

The failure is exactly operator-norm leakage of the named low-energy
direction, not a missing spectral gap.  Let
\[
 \Delta_n={1\over |Q|}\sum_{q\in Q}
 (I-\operatorname{Ad}u_{q,n})^*(I-\operatorname{Ad}u_{q,n}),
 \qquad P_{\eta,n}=1_{[0,\eta]}(\Delta_n),
\]
and
\[
 \nu_{\eta,n}
 =\|(I-P_{\eta,n})\operatorname{Ad}u_{t,n}P_{\eta,n}\|_{2\to2}.
                                                                  \tag{KPL8}
\]
For every choice \(\eta_n\downarrow0\) with
\[
 \frac{\max_{q\in Q}\|[B_{o,n},u_{q,n}]\|_2}
      {\sqrt{\eta_n}}\longrightarrow0,
\]
the one-row spectral estimate forces
\[
             \liminf_n\nu_{\eta_n,n}\geq{\sqrt2\over4}.   \tag{KPL9}
\]
Property \((T)\) and its robust finite-dimensional spectral gap therefore
do not imply compressor normalization in \(2\to2\) norm, even for the named
Pauli unitary.  They can control the normalized number of leaking adjoint
directions while the single full-rank unitary \(B_o\) occupies an
exceptional direction of vanishing adjoint density.

This does not construct a countermodel for the full Kun--Thom actor
\[
 \operatorname{EL}_r(\mathbb F_q[x_1^{\pm1},\ldots,x_d^{\pm1}])
 \rtimes\operatorname{SL}_d(\mathbb Z).
\]
That distinction is load-bearing.  Two explicit positive compressors
already generate the full actor, while every one-compressor restriction has
the countermodel above.  Hence the remaining theorem must use simultaneous
relations between at least two compressor directions (equivalently, the
nonamenable \(\operatorname{SL}_d(\mathbb Z)\) coherence); no argument using
one compression chain, one Kazhdan expander, or average low-spectrum
counting can close the shared sign.
