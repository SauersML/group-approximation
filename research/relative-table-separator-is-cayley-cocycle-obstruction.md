---
rg: 2
id: relative-table-separator-is-cayley-cocycle-obstruction
kind: claim
title: A relative table separator is exactly a nonlinear Cayley cocycle obstruction
artifacts:
  - research/transport-separator-through-relative-unitary-zero-cochains.md
distinct_from:
  relative-pd-body-has-table-or-separator-dichotomy: that produces a metric separator abstractly; this transports its margin through every relative unitary table and identifies the surviving nonlinear cocycle.
  finite-positive-definite-window-is-a-relative-corner-selector: that turns one low-energy unitary table into a corner; this gives the exact dual lower bound on the energy of every such table.
  tfd-low-leakage-compressions-flexibly-reduce: that applies property TFD after an exact ambient representation is supplied; this proves why the twisted transport tuple is still only an Iwahori pair and therefore lies before that theorem.
---

Use the finite quotient \(G\), core \(B<G\), core representation
\(\beta:B\to U(d)\), marked tuple \(U=(U_s)_{s\in S}\), and a norm-one
separator \(Z=(Z_s)_{s\in S}\) satisfying
\[
 \langle Z,U\rangle-
 \sup_{C\in\mathcal C(G,B,\beta)}\langle Z,C\rangle
 \geq\delta>0.                                           \tag{RCO1}
\]
Let \(\mathcal W_\beta\) be the relative unitary zero-cochains
\[
 \mathcal W_\beta=
 \{W:G\to U(d):W_e=1,\ W_{bg}=\beta(b)W_g
   \text{ for }b\in B,g\in G\}.                          \tag{RCO2}
\]
Define their twisted Cayley coboundary energy by
\[
 \mathcal E_U(W)^2=
 \frac1{|S||G|}
 \sum_{s\in S}\sum_{g\in G}
 \|U_sW_g-W_{sg}\|_{2,d}^2.                              \tag{RCO3}
\]

Then every relative zero-cochain obeys
\[
 \mathcal E_U(W)\geq\delta.                              \tag{RCO4}
\]
More precisely, put
\[
 C_s(W)=\frac1{|G|}\sum_{g\in G}W_{sg}W_g^*.
\]
The tuple \(C(W)\) lies in \(\mathcal C(G,B,\beta)\), and one has the exact
transport identity
\[
 \begin{aligned}
 \langle Z,U-C(W)\rangle
  &=
 \frac1{|S||G|}\sum_{s,g}
 \operatorname{Re}\operatorname{tr}_d
 \bigl((Z_sW_g)^*(U_sW_g-W_{sg})\bigr).                  \tag{RCO5}
 \end{aligned}
\]
The transported dual cochain \((Z_sW_g)_{s,g}\) has norm one, so
(RCO1), (RCO5), and Cauchy--Schwarz give (RCO4).

There is an exact representation-theoretic interpretation. On
\[
 \mathscr K=\ell^2(G)\otimes M_d
\]
define the twisted shifts
\[
 (\mathcal T_s f)(g)=U_sf(s^{-1}g).                       \tag{RCO6}
\]
Every \(\mathcal T_s\) is unitary and
\[
 \mathcal E_U(W)^2=
 \frac1{|S|}\sum_{s\in S}
 \|\mathcal T_sf_W-f_W\|_{2,\mathscr K}^2,
 \qquad f_W(g)=W_g.                                      \tag{RCO7}
\]
The \(\mathcal T_s\) satisfy each modular-vertex presentation exactly, and
their two Iwahori edge restrictions have exactly the same normalized
Hilbert--Schmidt defect as the original tuple \(U\). Thus they are an
amplified exact-vertex Iwahori pair, not an exact representation of \(A\)
before the missing multiplication rows are filled.

Consequently property \((T;FD)\) does not contradict (RCO4): it gives a
gap for exact finite-dimensional representations of \(A\), while
\(\mathcal T\) becomes such a representation only after the very edge/table
defects at issue have been removed. A failed capture sequence therefore
produces a positive nonlinear relative Cayley cosystole
\[
 \inf_{W\in\mathcal W_{\beta_n}}\mathcal E_{U_n}(W)
 \geq c>0                                                \tag{RCO8}
\]
despite vanishing presentation defect. Proving that the two concrete
Iwahori cubic rows force the left side to vanish is now an exact equivalent
transport problem. No such estimate is proved here; the root remains open.

DERIVATION
transport-separator-through-relative-unitary-zero-cochains
