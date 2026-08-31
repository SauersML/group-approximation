---
rg: 2
id: multi-kraus-frame-energy-is-the-full-relative-pd-gate
kind: claim
title: Multi-Kraus frame energy exactly metrizes the full relative positive-definite gate
artifacts:
  - research/stinespring-components-give-frame-energy-and-dual-transport.md
distinct_from:
  relative-table-separator-is-cayley-cocycle-obstruction: that tests only flat unitary-valued zero-cochains; this metrizes the entire relative coefficient body by arbitrary rectangular Stinespring frames.
  relative-pd-body-has-table-or-separator-dichotomy: that defines the coefficient-body distance and produces its metric separator; this gives an exact nonlinear Dirichlet realization of that distance.
  almost-full-hecke-frame-gives-flexible-corner: that starts from a near-top almost-full frame and fills its missing corner; this identifies the unrestricted frame energy which is exactly equivalent to coefficient-body feasibility.
---

Use the finite quotient \(G\), core \(B<G\), core representation
\(\beta:B\to U(d)\), marked set \(S\), prescribed unitaries
\(U=(U_s)_{s\in S}\), relative coefficient body
\(\mathcal C(G,B,\beta)\), and distance \(\Delta(U)\) from (TPD1)--(TPD2).

A relative Stinespring frame is a finite family of maps
\[
 A_g:\mathbb C^d\longrightarrow\mathbb C^r\qquad(g\in G)  \tag{MKF1}
\]
for some unrestricted \(r\), satisfying
\[
 \sum_{g\in G}A_g^*A_g=1,\qquad
 A_{bg}=A_g\beta(b)^*\quad(b\in B,g\in G).                \tag{MKF2}
\]
Its coefficient table and marked-row energy are
\[
 F_A(k)=\sum_{g\in G}A_{kg}^*A_g,                         \tag{MKF3}
\]
\[
 \mathcal E_U^{\mathrm K}(A)^2
 =\frac1{|S|}\sum_{s\in S}\sum_{g\in G}
   \frac1d\|A_{sg}U_s-A_g\|_{\mathrm F}^2.                \tag{MKF4}
\]
Then the relative coefficient body is exactly the set of restrictions
\((F_A(s))_{s\in S}\) of such frames, and
\[
 \Delta(U)\ \leq\
 e_{\mathrm K}(U):=\inf_A\mathcal E_U^{\mathrm K}(A)
 \ \leq\ \sqrt{\Delta(U)^2+2\Delta(U)}.                  \tag{MKF5}
\]
In particular,
\[
 e_{\mathrm K}(U_n)\longrightarrow0
 \quad\Longleftrightarrow\quad
 \Delta(U_n)\longrightarrow0.                            \tag{MKF6}
\]
For every individual frame there is the exact row identity
\[
 \mathcal E_U^{\mathrm K}(A)^2
 =\frac1{|S|}\sum_s
 \left(\|U_s-F_A(s)\|_{2,d}^2+1-\|F_A(s)\|_{2,d}^2\right). \tag{MKF7}
\]

The metric separator also transports through every multi-Kraus frame, not
only through a unitary table. If \(Z=(Z_s)\) has direct-sum normalized
Hilbert--Schmidt norm one, then
\[
 \begin{aligned}
 \langle Z,U-F_A\rangle
  =\frac1{|S|}\sum_{s,g}\frac1d
   \operatorname{Re}\operatorname{Tr}
   \left((A_{sg}Z_s)^*(A_{sg}U_s-A_g)\right),             \tag{MKF8}
 \end{aligned}
\]
and
\[
 \frac1{|S|}\sum_{s,g}\frac1d\|A_{sg}Z_s\|_{\mathrm F}^2=1. \tag{MKF9}
\]
Thus a norm-one separator of margin \(\delta\) forces
\[
 \mathcal E_U^{\mathrm K}(A)\geq\delta
 \quad\hbox{for every relative Stinespring frame }A.      \tag{MKF10}
\]

Combined with (TPD3), any estimate forcing \(e_{\mathrm K}(U)\to0\) from the
two concrete Iwahori row defects is sufficient for congruence capture.
Conversely, a positive capture gap forces a positive multi-Kraus cosystole.
This is the full positive-definite gate. On a general finite group the
unitary-table energy in (RCO3) is only its flat rank-\(d\) subproblem.

The needed flattening theorem is now available for the present quotient
family. Right-translation-flattens-every-relative-kraus-frame first
normalizes every frame to tall isometries, and
cayley-expansion-aligns-isometry-frame-coranges then gives
\[
 e_{\mathrm K}(U)=e_{\rm iso}(U)\leq e_{\rm unit}(U)
 \leq\left(1+2\sqrt{2/\gamma}\right)e_{\mathrm K}(U)
\]
on every quotient with Cayley Poincare gap \(\gamma\). Property
\((T;FD)\) makes \(\gamma\) uniform for the authenticated quotients.
Thus unitary and full multi-Kraus vanishing are equivalent here. No
estimate from the concrete Iwahori cubics to either energy is proved;
the root remains open.

DERIVATION
stinespring-components-give-frame-energy-and-dual-transport
