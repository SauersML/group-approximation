---
rg: 2
id: optimized-core-full-pd-energy-is-intrinsic-selector
kind: claim
title: Optimized-core full-PD energy is the intrinsic relative selector
artifacts:
  - research/move-core-then-round-a-full-kraus-corner.md
distinct_from:
  gauge-optimized-induced-energy-target: that minimizes the energy of one chosen Schreier-section table after moving the core; this minimizes over the entire relative positive-definite body and is therefore section-independent and no stronger than necessary.
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that freezes one prescribed core; this takes the infimum over all exact nearby BS core coordinates before applying the full-PD gate.
  cyclic-core-twist-forces-full-relative-cayley-cosystole: that proves every fixed-core selector stays far on a harmless twist; this optimized functional absorbs that family at its true vanishing core-motion scale.
---

Fix a finite one-power endpoint
\[
 G_N=A_N,\qquad B_N=\langle r,t\rangle<G_N
\]
and a dimension \(d\). Let \(\mathcal C_N(d)\) be the exact core variety
from (GOI2). For an exact supplied core \(b=(R,T)\), an extender \(X\),
and a competitor \(c=(R_c,T_c)\in\mathcal C_N(d)\), put
\[
 U_c=(X,R_c,T_c),\qquad
 m(b,c)=\|R-R_c\|_2^2+\|T-T_c\|_2^2.                     \tag{OPD1}
\]
Let \(e_{\rm K}(U_c;c)\) be the full relative Kraus energy for the core
representation determined by \(c\), and let \(e_{\rm unit}(U_c;c)\) be
the corresponding relative unitary-table energy. Define
\[
 \mathfrak E_{\rm K}(X,b)
 =\inf_{c\in\mathcal C_N(d)}
   \left(m(b,c)+e_{\rm K}(U_c;c)^2\right),                \tag{OPD2}
\]
\[
 \mathfrak E_{\rm unit}(X,b)
 =\inf_{c\in\mathcal C_N(d)}
   \left(m(b,c)+e_{\rm unit}(U_c;c)^2\right).             \tag{OPD3}
\]

If the Cayley Poincare gap of \(G_N\) is at least \(\gamma>0\), then
\[
 \mathfrak E_{\rm K}
 \leq\mathfrak E_{\rm unit}
 \leq\left(1+2\sqrt{\frac2\gamma}\right)^2
      \mathfrak E_{\rm K}.                               \tag{OPD4}
\]
Thus optimizing the exact core commutes, up to one dimension-free
constant, with passing from the complete positive-definite body to flat
unitary tables. Property \((T;FD)\) makes the same constant work for all
authenticated Iwahori quotients.

There is a constant \(C\), depending only on the fixed marked set and the
property-\((T;FD)\) gap, such that
\[
 D_{\rm flex}(X,R,T)
 \leq C\sqrt{\mathfrak E_{\rm K}(X,b)}.                   \tag{OPD5}
\]
The finite-dimensional Stinespring target and all endpoint representations
produced here factor through \(G_N\). Hence
\[
 \mathfrak E_{\rm K}(X_n,b_n)\longrightarrow0            \tag{OPD6}
\]
is an intrinsic, section-free sufficient criterion for flexible congruence
repair.

Conversely, every same-dimensional exact endpoint
\(\rho:G_N\to U(d)\) supplies the competitor
\[
 c=(\rho(r),\rho(t))
\]
and the flat table \(W_g=\rho(g)\). Consequently
\[
 \mathfrak E_{\rm unit}(X,b)
 \leq \|R-\rho(r)\|_2^2+\|T-\rho(t)\|_2^2
      +\|X-\rho(x)\|_2^2,                                \tag{OPD7}
\]
up to the harmless fixed normalization of the marked energy. Thus, at a
fixed dimension, \(\sqrt{\mathfrak E_{\rm K}}\) metrizes distance to the
union of exact endpoint fibers up to uniform constants. Flexible padding
can be incorporated by taking the same infimum after admissible
amplification and charging its relative rank.

The functional strictly improves the chosen-section target. For every
core competitor \(c\), the Schreier table used in (GOI4) is one admissible
relative unitary zero-cochain. Therefore
\[
 \mathfrak E_{\rm K}\leq\mathfrak E_{\rm unit}
 \leq C_S\,G_N(X,b),                                     \tag{OPD8}
\]
where \(C_S\) only converts the maximum in (GOI4) to the fixed marked
average. The proposed estimate (GOI5) implies the intrinsic estimate, but
the converse is not asserted: a badly conditioned section need not
represent the best positive-definite table.

Both known frozen-core obstructions disappear at the correct scale.

1. For the cyclic twist (CCT8), choose the untwisted core
   \(c=(\rho_K(r),\rho_K(t))\). The hybrid tuple is the exact endpoint, so
   \[
    \mathfrak E_{\rm K}\leq\mathfrak E_{\rm unit}
    \leq|\zeta_K-1|^2.                                   \tag{OPD9}
   \]
2. For the endpoint-conjugation family (OCA1), choose the conjugated core
   \(c_z=(zRz^{-1},zTz^{-1})\). Again the hybrid is exact, and
   \[
    \mathfrak E_{\rm K}\leq
    \|zRz^{-1}-R\|_2^2+\|zTz^{-1}-T\|_2^2.               \tag{OPD10}
   \]

Accordingly the fixed-core cubic-to-Cayley implication is replaced by the
precise remaining question
\[
 \mathfrak E_{\rm K}(X,b)\leq
 C\,E_{\rm end}(X,b)                                     \tag{OPD11}
\]
uniformly in \(N\) and \(d\). This is weaker than the open chosen-section
estimate (UGO1) but still sufficient by (OPD5). No proof of (OPD11) is
given here; the root remains open.

DERIVATION
move-core-then-round-a-full-kraus-corner
