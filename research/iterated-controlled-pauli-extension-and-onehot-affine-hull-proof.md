---
rg: 2
id: iterated-controlled-pauli-extension-and-onehot-affine-hull-proof
kind: route
title: Compute the affine residue and extend every sector through all D8 cells
target: d8-per-projection-synchronous-compiler-affine-hull-transparent
requires:
  - controlled-pauli-reflection-dilation-hyperlinear-d8-absorber
  - central-block-hecke-predicates-force-affine-group-spectra
---

# Compute the affine residue and extend every sector through all D8 cells

## 1. Product equations cut out exactly the affine hull

Identify a sign vector \(\epsilon\in\{\pm1\}^k\) with
\(x\in\mathbf F_2^k\) by

\[
 \epsilon_i=(-1)^{x_i}.
 \tag{1}
\]

A product equation

\[
 \prod_{i\in S}\epsilon_i=(-1)^b
 \tag{2}
\]

is exactly the affine linear equation

\[
 \sum_{i\in S}x_i=b
 \quad\text{in }\mathbf F_2.
 \tag{3}
\]

Let \(R\subseteq\mathbf F_2^k\) be nonempty.  Choose \(x_0\in R\) and let

\[
 V=\operatorname{span}\{x-x_0:x\in R\}.
 \tag{4}
\]

An affine functional vanishes on \(R\) exactly when its linear part
annihilates \(V\) and its constant is fixed by its value at \(x_0\).
Therefore the common solution set of every affine equation valid on \(R\)
is

\[
 x_0+V=\operatorname{Aff}_{\mathbf F_2}(R).
 \tag{5}
\]

Equations made from products of commuting involutions are precisely (2).
This proves that all such group equations retain exactly the affine hull.

For a synchronous relation \(R\subseteq A\times B\), use the outcome
indicator vector

\[
 (e_a)_{a\in A}\mathbin{\|}(e_b)_{b\in B}
 \in\mathbf F_2^{A\sqcup B}.
 \tag{6}
\]

The same calculation applies to the finite set of indicator vectors
corresponding to allowed pairs.  Thus adding all product relations valid on
the synchronous predicate gives its affine hull in indicator coordinates,
not the predicate itself.

## 2. One-hot PVM relations leave every odd sector

Let \(P_1,\ldots,P_n\) be a PVM and put

\[
 w_a=1-2P_a.
 \tag{7}
\]

The projections commute, hence so do the \(w_a\).  On the range of \(P_b\),
exactly the factor \(w_b\) acts by \(-1\), while every other factor acts by
\(1\).  Thus

\[
 \prod_{a=1}^n w_a=-1.
 \tag{8}
\]

Conversely, take any scalar signs \(\epsilon_a=(-1)^{x_a}\).  Relations
consisting of commutation, involutivity, and (8) say only

\[
 \sum_a x_a=1.
 \tag{9}
\]

The one-hot vectors are \(e_1,\ldots,e_n\).  Their differences from \(e_1\)
span the even-parity subspace:

\[
 \operatorname{span}\{e_a+e_1:2\leq a\leq n\}
 =\left\{v:\sum_av_a=0\right\}.
 \tag{10}
\]

Hence their affine hull is the odd-parity hyperplane

\[
 e_1+\left\{v:\sum_av_a=0\right\}
 =\left\{x:\sum_ax_a=1\right\}.
 \tag{11}
\]

For \(n=2\), (11) is the one-hot set.  For every \(n\geq3\), it also
contains vectors of Hamming weight three, and for larger \(n\) every
available odd weight.  On such a scalar sector the expressions

\[
 \frac{1-w_a}{2}
 \tag{12}
\]

equal \(1\) for several outcomes simultaneously.  They are not orthogonal
PVM atoms even though every commuting-product relation true on a PVM is
satisfied.

## 3. All D8 cells extend simultaneously

Let \(G\) be any group and let \(r_1,\ldots,r_m\) be nontrivial
involutions.  Form the iterated amalgam

\[
 \Gamma
 =G*_{\langle r_1\rangle}D_8^{(1)}
   *_{\langle r_2\rangle}D_8^{(2)}
   *\cdots*
   _{\langle r_m\rangle}D_8^{(m)},
 \tag{13}
\]

where the edge maps identify \(r_i\) with the central commutator \(z_i\) in
the \(i\)-th cell.  Bass--Serre normal form embeds every vertex, in
particular \(G\).

Let \(\pi:G\to\mathcal U(H)\).  Work on

\[
 \widetilde H=H\otimes(\mathbf C^2)^{\otimes m}.
 \tag{14}
\]

For each \(i\), set

\[
 W_i=\pi(r_i),\qquad P_i=\frac{1-W_i}{2},
 \tag{15}
\]

and on the \(i\)-th fresh qubit define

\[
 U_i=(1-P_i)\otimes I+P_i\otimes X_i,\qquad
 V_i=(1-P_i)\otimes I+P_i\otimes Z_i.
 \tag{16}
\]

Identity operators on all unmentioned tensor factors are implicit.
The one-cell calculation gives

\[
 U_i^2=V_i^2=1,\qquad [U_i,V_i]=W_i.
 \tag{17}
\]

There are no relations between distinct D8 vertices beyond their common
base \(G\).  Thus possible noncommutation among the control projections
\(P_i\) is irrelevant, and (16) defines one representation of the whole
iterated amalgam.  Its restriction to \(G\) is

\[
 \pi\otimes I_{2^m}.
 \tag{18}
\]

If \(\pi\) is finite dimensional, so is the extension.  If \(\pi\) is a
tracial representation, tensoring by normalized matrix trace preserves all
old moments.  In particular, no spectral sector of \(G\) is removed.

Apply this with \(G=G_{\rm aff}\), the solution group of all affine
consequences of the synchronous supports.  Every forbidden point in an
affine hull which extends to a scalar character of the global solution
group gives, through (14)--(18), an exact finite-dimensional representation
of the D8 compiler.  More generally, every operator-valued representation
of \(G_{\rm aff}\) extends, so the conclusion does not rely on the
existence of a scalar global assignment.

## 4. Hyperlinearity and finite presentation are unchanged

Each edge group in (13) is \(C_2\), and each new vertex \(D_8^{(i)}\) is
finite.  If \(G\) is hyperlinear, repeated amenable-edge amalgam
permanence makes \(\Gamma\) hyperlinear.  Conversely \(G\) is a subgroup of
\(\Gamma\), so hyperlinearity of \(\Gamma\) implies that of \(G\).  Hence

\[
 \Gamma\text{ hyperlinear}\quad\Longleftrightarrow\quad
 G\text{ hyperlinear}.
 \tag{19}
\]

If \(G\) has a finite presentation, adjoining the two noncentral
involutions of each D8 cell and its finite relation list gives a finite
presentation of \(\Gamma\).

If a proposed cell is attached to a word which is already trivial in \(G\),
the cell factors through the finite quotient \(D_8/\langle z\rangle\).
Such a degenerate finite attachment cannot impose a predicate either; the
nontrivial-involution assumption merely keeps (13) in the standard
injective Bass--Serre form.

## 5. Coupling the cells returns to the same dichotomy

Separate D8 vertices are completely transparent by Section 3.  Suppose
instead that one tries to place the commuting selector reflections and all
actors in one finite group \(K\), choose a central character \(\lambda\),
and require that the selected block \(p_\lambda\mathbf C[K]\) contain only
one irreducible type.  The unique-central-block character theorem says that
the restriction of this type to the abelian selector subgroup is the full
torsor of compatible characters, with equal multiplicities.  Its Boolean
joint support is affine.

Thus:

\[
 \begin{array}{c|c}
 \text{separate D8 cells}&\text{every affine sector extends},\\
 \text{one unique finite central block}&\text{joint support is affine}.
 \end{array}
 \tag{20}
\]

Allowing the intended predicate projections to remain arbitrary diagonal
Hecke sums realizes the local predicate, but those sums are not elements of
the selector group and cannot be identified across contexts by an ordinary
group relator.  This is precisely the signed-Hecke/root-kernel gate.  The
per-projection D8 construction does not cross it.
