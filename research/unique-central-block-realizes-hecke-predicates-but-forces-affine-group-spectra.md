---
rg: 2
id: unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra
kind: claim
title: A unique finite central block realizes every predicate as Hecke data but forces every group-native joint spectrum to be affine
distinct_from:
  finite-selector-gadget-induction-barrier: that shows induction recreates every central selector character in some irreducible sector; this removes all hidden sectors by making the selected central block simple, then proves that simplicity itself forces flat affine spectra for commuting group elements.
  true-bcs-predicates-are-local-finite-group-corners: that realizes an arbitrary predicate in a corner of an elementary abelian group algebra but uses a corner with many one-dimensional types; this gives an augmentation-zero Heisenberg block with exactly one selected irreducible type.
  controlled-central-phase-finite-group-barrier: that rules out a nonlinear scalar central phase over Boolean selectors; this permits arbitrary nonlinear diagonal Hecke projections, and locates the obstruction precisely at requiring those coordinates to be actual group elements.
  one-center-heisenberg-tree-has-no-proper-escaped-marginal: that classifies finite-type partitions across a tree of prime Heisenberg charts; this is a one-vertex character theorem for every finite group with a simple central-character block.
---

**EXACT LOCAL SIGNED-HECKE COMPILER AND SHARP GROUP-NATIVE NO-GO;
NO NONHYPERLINEAR GROUP IS CLAIMED.**

Let \(K\) be a finite group, let \(Z\leq Z(K)\), and let
\(\lambda\in\widehat Z\).  Put

\[
 p_\lambda=\frac1{|Z|}\sum_{z\in Z}\overline{\lambda(z)}z.
 \tag{UCB1}
\]

Assume that the selected block is simple:

\[
 p_\lambda\mathbf C[K]\cong M_d(\mathbf C).
 \tag{UCB2}
\]

Equivalently, there is exactly one irreducible \(K\)-representation
\(\rho\) with central character \(\lambda\).  Necessarily

\[
 d^2=[K:Z].
 \tag{UCB3}
\]

Then the character of \(\rho\) is forced:

\[
 \chi_\rho(g)=
 \begin{cases}
 d\lambda(g),&g\in Z,\\
 0,&g\notin Z.
 \end{cases}
 \tag{UCB4}
\]

Consequently, for every abelian subgroup \(H\leq K\), every character
\(\eta\in\widehat H\) occurs in \(\rho|_H\) with multiplicity

\[
 m_\eta=
 \begin{cases}
 d/[H:H\cap Z],&\eta|_{H\cap Z}=\lambda|_{H\cap Z},\\
 0,&\text{otherwise}.
 \end{cases}
 \tag{UCB5}
\]

Thus the support of \(\rho|_H\) is the **entire** affine torsor of
characters extending the prescribed central character, and all its atoms
have the same rank.

In particular, let \(s_1,\ldots,s_k\in K\) be commuting involutions and let

\[
 R_\rho(s_1,\ldots,s_k)
 =\{(\eta(s_1),\ldots,\eta(s_k)):m_\eta>0\}
 \subseteq\{\pm1\}^k.
 \tag{UCB6}
\]

Then \(R_\rho(s_1,\ldots,s_k)\) is an affine subspace of the Boolean cube.
If the \(s_i\) generate \(H\), it has cardinality \([H:H\cap Z]\), and every
joint eigenspace has rank \(d/[H:H\cap Z]\).  The same statement for
commuting finite-order elements says that their joint spectrum is a coset
of a finite subgroup of the product of their root-of-unity groups.

There is nevertheless a positive local result at the Hecke-operator level.
For every nonempty finite relation \(R\subseteq A\times B\), choose an
integer \(D\geq\max(2,|R|)\) and a surjection

\[
 \theta:\{0,\ldots,D-1\}\longrightarrow R.
 \tag{UCB7}
\]

The finite Heisenberg group

\[
 H_D=\langle x,y,z\mid x^D=y^D=z^D=1,\ z\ {\rm central},\
 yx=zxy\rangle
 \tag{UCB8}
\]

has order \(D^3\).  For the primitive character
\(\lambda(z)=\exp(2\pi i/D)\),

\[
 p_\lambda\mathbf C[H_D]\cong M_D(\mathbf C)
 \tag{UCB9}
\]

and this block has one irreducible representation.  In its Schrödinger
basis \(e_t\), \(t\in\mathbf Z/D\mathbf Z\), define

\[
 P_a=\sum_{\theta(t)=(a,b)\ {\rm for\ some}\ b}|e_t\rangle\langle e_t|,
 \qquad
 Q_b=\sum_{\theta(t)=(a,b)\ {\rm for\ some}\ a}|e_t\rangle\langle e_t|.
 \tag{UCB10}
\]

Then \((P_a)_a\) and \((Q_b)_b\) are commuting PVMs in the single
augmentation-zero block, and

\[
 P_aQ_b\neq0\quad\Longleftrightarrow\quad(a,b)\in R.
 \tag{UCB11}
\]

Hence finite Stone--von Neumann theory **does** eliminate every hidden
central-character irreducible while realizing an arbitrary predicate as
signed Hecke data.

Equations (UCB5)--(UCB6) give the exact obstruction to turning this local
construction into a solution-group or subgroup-amalgamation compiler.  If
the coordinate measurements in (UCB10) were spectral projections of
commuting group elements in the same simple block, their joint support
would have to be affine.  For a nonaffine \(R\), at least one of the
following is unavoidable:

1. the selected central block has another irreducible sector;
2. the predicate coordinates are genuine group-algebra/Hecke operators,
   not group elements; or
3. one abandons a finite simple central selector block.

A normal Heisenberg subgroup only proves that selected representations are
isotypic **on that normal subgroup**.  Extension elements still act on an
external Clifford multiplicity space; making the whole selected block
simple returns to (UCB4)--(UCB6).  Therefore a finite central-type selector
solves the local hidden-sector problem exactly, but it cannot also give
group-native nonlinear predicate gluing.  The surviving gate is a finite
presentation which identifies the Hecke projections (UCB10) across
overlapping contexts without replacing those linear combinations by group
elements and without losing the positive canonical block trace.

DERIVATION
central-block-character-vanishing-and-flat-restriction-proof
