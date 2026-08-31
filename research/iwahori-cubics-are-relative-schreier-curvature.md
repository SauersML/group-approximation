---
rg: 2
id: iwahori-cubics-are-relative-schreier-curvature
kind: claim
title: The two Iwahori cubics are exact relative Schreier curvature
artifacts:
  - research/collapse-core-edges-and-gauge-a-schreier-tree.md
distinct_from:
  word-section-fillings-obstruct-matrix-ulam-input: that bounds one word-section table by van Kampen area; this identifies the exact finite connection, its holonomy on every relator, and the tree-gauge normal form of every relative unitary table.
  finite-schreier-holonomy-is-the-lamp-gauge-obstruction: that compares two block connections arising from a lamp normalizer; this collapses an exact subgroup core and identifies the Iwahori cubic rows as the remaining triangular curvature.
  cyclic-core-twist-forces-full-relative-cayley-cosystole: that supplies the quantitative counterfamily; this explains geometrically why its small local curvature retains macroscopic fundamental holonomy.
---

Let \(G=\langle S\rangle\) be finite, let \(B<G\), let
\(\beta:B\to U(d)\), and choose a section
\[
 \tau:Q=B\backslash G\longrightarrow G,\qquad\tau(B)=e. \tag{RSC1}
\]
Write every \(g\in G\) uniquely as
\[
 g=k(g)\tau(q(g)),\qquad k(g)\in B,\quad q(g)\in Q.       \tag{RSC2}
\]
For every \(s\in S\), \(b\in B\), and \(q\in Q\), write
\[
 sb\tau(q)=b'\tau(q')                                    \tag{RSC3}
\]
and attach to the directed edge
\[
 e=(s;b,q):q\longrightarrow q'
\]
the unitary transport
\[
 K_e=\beta(b')^*U_s\beta(b).                             \tag{RSC4}
\]
These edges form a connected finite Schreier multigraph
\(\mathscr S_\tau\). The equivalent right-coset convention is obtained by
inverting every group coordinate.

Every relative unitary zero-cochain is uniquely determined by
\[
 Y_q=W_{\tau(q)},\qquad W_{b\tau(q)}=\beta(b)Y_q,          \tag{RSC5}
\]
and its Cayley energy has the exact connection form
\[
 \mathcal E_U(W)^2
 =\frac1{|S||B||Q|}\sum_{e=(s;b,q)}
   \|K_eY_q-Y_{q'}\|_{2,d}^2.                            \tag{RSC6}
\]
Thus the unitary selector is a nonabelian synchronization problem on
\(\mathscr S_\tau\), not merely a word-length problem.

If a path starts at \(b_0\tau(q_0)\), has successive letters
\(s_1,\ldots,s_\ell\), and ends at \(b_\ell\tau(q_\ell)\), then its
ordered transport satisfies the exact telescope
\[
 K_{e_\ell}\cdots K_{e_1}
 =\beta(b_\ell)^*U_{s_\ell\cdots s_1}\beta(b_0).          \tag{RSC7}
\]
In particular, a presentation relator \(w=e\) has, at every starting
fiber, holonomy unitarily conjugate to \(U_w\). Its curvature norm is
exactly
\[
 \|\operatorname{Hol}_w-1\|_{2,d}=\|U_w-1\|_{2,d}.        \tag{RSC8}
\]

In the square-free Iwahori presentation, take
\(B=\langle r,t\rangle\) and assume its representation is exact. Every
\(r\)- or \(t\)-edge in (RSC4) is then an identity self-edge after the
core is collapsed. Consequently
\[
 (xt)^3,\qquad(xt^2r)^3                                 \tag{RSC9}
\]
become two families of triangular \(x\)-edge faces in
\(\mathscr S_\tau\), and their matrix holonomies are respectively
\[
 \beta(b)^*(XT)^3\beta(b),\qquad
 \beta(b)^*(XT^2R)^3\beta(b).                            \tag{RSC10}
\]
The involution and inversion rows similarly give the collapsed digons.
This is the exact discrete-curvature meaning of the two cubic rows.

Choose any spanning tree of \(\mathscr S_\tau\). There is a gauge
\((Y_q)\), normalized by \(Y_B=1\), which makes every tree edge exact.
For a chord \(e\), its remaining row error is exactly the normalized
Hilbert--Schmidt distance of the fundamental-cycle holonomy from one.
If that cycle has a relative van Kampen filling with \(A(e)\) defective
cells and all marked relators have defect at most \(\delta\), then
\[
 \|K_eY_q-Y_{q'}\|_{2,d}\leq A(e)\delta.                 \tag{RSC11}
\]
Averaging (RSC11) is precisely the RMS filling estimate behind (WSF4).

Uniform one-skeleton expansion does not improve (RSC11) to a
dimension-free curvature modulus. The cyclic core-twist family has
uniform property-\((T;FD)\) Cayley gap, both nontrivial local curvatures
of size \(O(K^{-1})\), yet
\[
 \inf_W\mathcal E_{U_K}(W)\geq\sqrt\gamma/2.              \tag{RSC12}
\]
Hence its fundamental holonomy cannot be gauged small; equivalently the
required relative filling area accumulates at the moving level. This is
an explicit twisted-connection counterexample to the proposed
spanning-tree-plus-expander proof with a frozen core.

After optimizing the exact core, the counterconnection becomes flat:
choosing the untwisted core in (OPD9) makes every holonomy one. Therefore
the viable remaining statement is a two-dimensional cosystolic estimate
modulo the exact core variety, namely (OPD11), not a curvature estimate
for one frozen Schreier connection. No such optimized estimate is proved
here, and the root remains open.

DERIVATION
collapse-core-edges-and-gauge-a-schreier-tree
