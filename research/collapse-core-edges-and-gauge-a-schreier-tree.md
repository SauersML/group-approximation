---
rg: 2
id: collapse-core-edges-and-gauge-a-schreier-tree
kind: route
title: Collapse exact core edges and gauge a relative Schreier spanning tree
target: iwahori-cubics-are-relative-schreier-curvature
requires:
  - relative-table-separator-is-cayley-cocycle-obstruction
  - word-section-fillings-obstruct-matrix-ulam-input
  - cyclic-core-twist-forces-full-relative-cayley-cosystole
---

# Relative cochains are gauges on a finite multigraph

After adjoining inverse letters and prescribing
\(U_{s^{-1}}=U_s^*\), every edge below has its adjoint reverse. Equation
(RSC2) gives a bijection
\[
 B\times Q\longrightarrow G,\qquad(b,q)\longmapsto b\tau(q).
\]
For \(g=b\tau(q)\), (RSC3) gives
\(sg=b'\tau(q')\). Substituting (RSC5) yields
\[
 \begin{aligned}
 U_sW_g-W_{sg}
 &=U_s\beta(b)Y_q-\beta(b')Y_{q'}\\
 &=\beta(b')\bigl(K_eY_q-Y_{q'}\bigr).                   \tag{1}
 \end{aligned}
\]
Unitary invariance of normalized Hilbert--Schmidt norm and the bijection
above prove (RSC6). Connectivity follows by projecting any Cayley path in
\(G\) to the section coordinates; multiple edges retain the missing
\(B\)-label which would be lost by pretending that left multiplication
acts on \(B\backslash G\).

# Path transports telescope exactly

Let
\[
 g_j=s_jg_{j-1}=b_j\tau(q_j).
\]
The transport on the \(j\)-th edge is
\[
 K_{e_j}=\beta(b_j)^*U_{s_j}\beta(b_{j-1}).
\]
All adjacent core factors cancel:
\[
 \begin{aligned}
 K_{e_\ell}\cdots K_{e_1}
 &=\beta(b_\ell)^*
   U_{s_\ell}\beta(b_{\ell-1})\beta(b_{\ell-1})^*
   U_{s_{\ell-1}}\cdots U_{s_1}\beta(b_0)\\
 &=\beta(b_\ell)^*U_{s_\ell\cdots s_1}\beta(b_0).         \tag{2}
 \end{aligned}
\]
If \(w=s_\ell\cdots s_1=e\) in \(G\), then \(g_\ell=g_0\), so uniqueness
in (RSC2) gives \(b_\ell=b_0\) and \(q_\ell=q_0\). Equation (2) becomes
(RSC7)--(RSC8).

If \(s\in B\), then \(q'=q\), \(b'=sb\), and exact core evaluation gives
\[
 K_e=\beta(sb)^*\beta(s)\beta(b)=1.                      \tag{3}
\]
Thus all core edges collapse without approximation. Apply (2) to the
words in (RSC9). Removing the identity transports from their alternating
core letters leaves three \(x\)-edges, and (RSC10) follows. Applying it
to \(x^2\) and \((xr)^2\) gives the corresponding digons.

# Tree gauge and fundamental holonomy

Choose a spanning tree, orient its paths away from the base vertex
\(B\), and set \(Y_B=1\). Recursively define
\[
 Y_{q'}=K_eY_q                                             \tag{4}
\]
on every oriented tree edge \(e:q\to q'\). For an edge used backwards,
use its adjoint reverse. Equation (4) makes all tree summands in (RSC6)
zero.

For a chord \(e:q\to q'\), let \(C_q\) and \(C_{q'}\) be the ordered
tree transports from the base. Then \(Y_q=C_q\) and \(Y_{q'}=C_{q'}\),
so
\[
 \|K_eY_q-Y_{q'}\|_{2,d}
 =\|C_{q'}^*K_eC_q-1\|_{2,d}.                            \tag{5}
\]
The unitary in (5) is exactly the holonomy around the fundamental loop
formed by the two tree paths and \(e\).

Suppose a word for that loop has a relative van Kampen decomposition
\[
 w=\prod_{j=1}^{A(e)} h_jr_j^{\varepsilon_j}h_j^{-1}
 \quad\text{modulo exact core words},                    \tag{6}
\]
where \(\varepsilon_j=\pm1\) and each \(r_j\) is a marked defective
relator. Evaluation of (6), (RSC7), and unitary conjugation show that the
holonomy is a product of \(A(e)\) unitaries, each at distance at most
\(\delta\) from one. The elementary product telescope
\[
 \|Z_1\cdots Z_m-1\|_2\leq\sum_j\|Z_j-1\|_2              \tag{7}
\]
proves (RSC11). Squaring and averaging (5)--(7) recovers the exact RMS
section-area loss.

# The expander step is one-dimensional and cannot fill curvature

The Cayley spectral gap can round a projection after a low-energy
cochain has been produced; it gives no bound on the fundamental
holonomies in (5). This separation is not only formal.
Cyclic-core-twist-forces-full-relative-cayley-cosystole supplies expanding
\(G_K\) and connections whose relator holonomies in (RSC8) tend to one,
while the infimum of (RSC6) stays at least \(\sqrt\gamma/2\). Thus no
modulus depending only on the one-skeleton gap and the maximum local
curvature can force a frozen-core tree gauge of small energy.

Changing the exact core changes every transport (RSC4), not merely the
choice of tree gauge. The optimized functional (OPD2) takes the infimum
over those connections before synchronizing them. On the cyclic family
one such connection is flat, which is why the fixed-core obstruction does
not survive (OPD11).
