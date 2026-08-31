---
rg: 2
id: transport-separator-through-relative-unitary-zero-cochains
kind: route
title: Transport the separator through every relative unitary zero-cochain
target: relative-table-separator-is-cayley-cocycle-obstruction
requires:
  - relative-pd-body-has-table-or-separator-dichotomy
  - finite-positive-definite-window-is-a-relative-corner-selector
---

# Relative unitary tables are points of the coefficient body

Fix \(W\in\mathcal W_\beta\) and define
\[
 F_W(k)=\frac1{|G|}\sum_{g\in G}W_{kg}W_g^*.             \tag{1}
\]
Let \(\lambda_G\) act on \(\ell^2(G)\) by left translation and set
\[
 V_W\xi=|G|^{-1/2}\sum_{g\in G}e_g\otimes W_g^*\xi.
\]
Then \(V_W\) is an isometry and
\[
 F_W(k)=V_W^*(\lambda_G(k)\otimes1)V_W.                  \tag{2}
\]
Therefore \(F_W\) is positive definite and \(F_W(e)=1\). Relative
equivariance gives
\[
 F_W(b)=\frac1{|G|}\sum_g\beta(b)W_gW_g^*=\beta(b)
 \quad(b\in B).                                          \tag{3}
\]
Hence \(C(W)=(F_W(s))_{s\in S}\) belongs to the body in (TPD1).

# The normal vector pairs exactly with the Cayley coboundary

Using the normalized real Hilbert--Schmidt pairing and cyclicity of trace,
\[
 \begin{aligned}
 \langle Z,U-C(W)\rangle
 &=
 \frac1{|S||G|}\sum_{s,g}
 \operatorname{Re}\operatorname{tr}_d
 \bigl(Z_s^*(U_s-W_{sg}W_g^*)\bigr)\\
 &=
 \frac1{|S||G|}\sum_{s,g}
 \operatorname{Re}\operatorname{tr}_d
 \bigl(W_g^*Z_s^*(U_sW_g-W_{sg})\bigr),
 \end{aligned}                                           \tag{4}
\]
which is (RCO5). Right multiplication by \(W_g\) preserves normalized
Hilbert--Schmidt norm, so
\[
 \frac1{|S||G|}\sum_{s,g}\|Z_sW_g\|_{2,d}^2
 =\frac1{|S|}\sum_s\|Z_s\|_{2,d}^2=1.                   \tag{5}
\]
Since \(C(W)\) is feasible, (RCO1) makes the left side of (4) at least
\(\delta\). Cauchy--Schwarz with (5) proves
\[
 \delta\leq\mathcal E_U(W).
\]
As \(W\) was arbitrary, this proves (RCO4).

# Twisted shifts preserve the unresolved Iwahori defect

Give \(\ell^2(G;M_d)\) the norm
\[
 \|f\|^2=\frac1{|G|}\sum_g\|f(g)\|_{2,d}^2.
\]
The operators in (RCO6) are unitary: left multiplication by \(U_s\) is
unitary on \(M_d\), and \(g\mapsto s^{-1}g\) is a permutation. Reindexing
gives
\[
 \|\mathcal T_sf_W-f_W\|^2
 =\frac1{|G|}\sum_h\|U_sW_h-W_{sh}\|_{2,d}^2,            \tag{6}
\]
and averaging (6) proves (RCO7).

For a word \(w=s_1\cdots s_\ell\),
\[
 (\mathcal T_wf)(g)=U_wf(w^{-1}g).                        \tag{7}
\]
Every defining relation inside either modular vertex is simultaneously a
relation for the exact vertex matrices \(U\) and for the quotient shifts.
Thus (7) is the identity for each vertex relator.

For an edge element \(b\), the two transported edge operators have the same
shift and differ only by left multiplication by
\[
 U_+(b)-U_-(\sigma b).
\]
On the Hilbert space \(M_d\), normalized Hilbert--Schmidt norm of the
left-multiplication operator \(L_X\) is
\[
 \|L_X\|_{2,M_d}=\|X\|_{2,d}.                             \tag{8}
\]
Tensoring with a permutation preserves this norm. Hence every transported
edge discrepancy has exactly the original normalized Hilbert--Schmidt
size.

The transport has therefore not created an exact representation to which a
property-\((T;FD)\) invariant-vector theorem could be applied. It has
replicated the original exact-vertex, defective-edge pair and turned a
relative table into a unitary-valued almost-invariant vector for that pair.
A uniform positive separator is exactly a uniform positive lower bound on
all such vectors' Dirichlet energy. This proves the surviving-cocycle
interpretation and isolates the missing nonlinear cosystolic estimate.
