---
rg: 2
id: tv-nested-conjugacy-bridge-boundary-proof
kind: route
title: Locate the nested-conjugacy bridge boundary at the TV dictator projector
target: nested-conjugacy-stops-at-tv-dictator-projectors
requires:
  - tv-zero-noise-cell-is-an-abelian-torsor
  - lcs-parity-gadgets-preserve-odd-dictator-affine-hull
---

# Locate the nested-conjugacy bridge boundary at the TV dictator projector

## 1. Exact scope of the 2025 bridge

Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao,
[arXiv:2510.04943v4](https://arxiv.org/html/2510.04943v4), prove two
different statements which must not be conflated.

Their [Lemma 3.12](https://arxiv.org/html/2510.04943v4#S3) starts with a
finitely presented group whose chosen generators are involutions.  It
computably embeds the group algebra into a BCS algebra obtained through a
solution-group construction, extends every tracial state, and supplies
controlled decompositions of the images of the group relators.

Their [Theorem
5.5](https://arxiv.org/html/2510.04943v4#S5.SS1) starts more generally with
a nested-conjugacy BCS.  It embeds that algebra into another BCS algebra,
again extends every tracial state, and gives the relation-decomposition
bound

$$
2^{16}M^2\ell^2\Lambda
$$

in the notation of that theorem.  The codomain asserted there is a BCS
algebra, not an LCS algebra.  In the proof, the ordinary BCS relation is
retained while Lemma 3.12 is applied to the flattened conjugacy relations.
Thus Lemma 3.12 groupifies the conjugacy scaffolding; it does not groupify
an arbitrary outer BCS predicate.

The rest of this route identifies which side of that boundary contains the
missing zero-noise Taller--Vidick constraint.

## 2. The zero-noise cell is already a group presentation

Fix one zero-noise Taller--Vidick outer cell and let \(P\) be its nonempty
projected satisfying-assignment support.  The elimination in
[tv-zero-noise-cell-torsor-elimination-proof](tv-zero-noise-cell-torsor-elimination-proof.md)
gives

$$
\Gamma_{\mathrm{cell}}
 \cong H\times\left(*_{q\in K/H}C_2\right),
\qquad
H\cong\{+1,-1\}^{P}.                                  \tag{1}
$$

For \(p\in P\), let \(\delta_p\in H\) be minus one at \(p\) and plus one
elsewhere, and put

$$
Q_p:=A_{\delta_p}.                                     \tag{2}
$$

The \(Q_p\)'s are commuting reflections.  Since the product of all
\(\delta_p\)'s is the constant-minus-one function \(z\), the folding
relation \(A_z=J\) becomes

$$
J=\prod_{p\in P}Q_p.                                   \tag{3}
$$

Consequently the \(J=-1\) scalar characters of this abelian factor are
indexed by the odd subsets \(\beta\subseteq P\): \(Q_p=-1\) exactly when
\(p\in\beta\).  The singleton subsets are precisely the honest dictator
characters.  Every odd subset of size at least three is a surviving
nondictator character.

All relations used to obtain (1)--(3) are group-word relations.  Applying
Lemma 3.12 to this finite presentation can re-encode the cell, but it cannot
remove any representation of the group it embeds.  In particular, it
cannot distinguish the singleton characters from the other odd characters.

## 3. The missing relation is a joint spectral projector

For every \(\beta\subseteq P\), define

$$
E_\beta
 =\prod_{p\in\beta}\frac{1-Q_p}{2}
  \prod_{p\notin\beta}\frac{1+Q_p}{2}.                 \tag{4}
$$

Because the \(Q_p\)'s commute, the \(E_\beta\)'s are their mutually
orthogonal joint spectral projections and sum to the identity.  Equation
(3) says that the \(J=-1\) corner is the sum of the \(E_\beta\)'s with
\(\lvert\beta\rvert\) odd.  Hence, inside that corner,

$$
E_\beta=0
\quad\text{for every odd }\lvert\beta\rvert\geq3       \tag{5}
$$

is equivalent to allowing exactly the singleton joint spectra.  This is the
exactly-one predicate on the commuting signs \(Q_p\).  It is an ordinary
BCS forbidden-assignment relation, but it is not a group-word relation.

This distinction is algebraic, not merely syntactic.

## 4. Affine obstruction to every involutory group-only encoding

Consider any finite group presentation whose generators, including any
auxiliaries, are involutions, with a distinguished central involution \(J\).
Assume that its visible generators include \(Q_p\), that \(J=-1\), and that
each singleton assignment to the \(Q_p\)'s has a scalar extension satisfying
all its group-word relations.

Write a scalar reflection as

$$
\rho(x)=(-1)^{v_x},
\qquad v_x\in\mathbb F_2.                              \tag{6}
$$

After scalarization, a word relation records only the parity with which
each generator occurs.  It is therefore a linear equation over
\(\mathbb F_2\), with the occurrence of \(J\) contributing its fixed
constant.  The scalar solution set in visible and auxiliary coordinates is
an affine subspace.  Its projection onto the visible \(Q_p\)-coordinates is
again affine.

Nested conjugacy does not alter this conclusion.  A reflection word of the
form

$$
x_\ell\cdots x_1x_0x_1\cdots x_\ell                 \tag{7}
$$

scalarizes to \(x_0\), because every outer sign occurs twice.  Any equality
between such monomials is still one affine parity equation.

Identify a subset \(\beta\subseteq P\) with its indicator vector in
\(\mathbb F_2^P\).  For any fixed \(p_0\in P\), the affine hull of all
singleton vectors is

$$
e_{p_0}
 +\operatorname{span}\{e_p+e_{p_0}:p\neq p_0\}
 =\left\{v\in\mathbb F_2^P:
          \sum_{p\in P}v_p=1\right\}.                  \tag{8}
$$

Thus any projected scalar solution set containing all honest singleton
profiles contains every odd profile.  When \(\lvert P\rvert\geq3\), it
contains a profile forbidden by (5).  Therefore no such group-only
presentation, even with existential involutory auxiliaries and nested
conjugacy relations, imposes (5) while retaining every singleton scalar
extension.

This is exactly the affine-hull obstruction proved in
[lcs-odd-dictator-affine-hull-no-go-proof](lcs-odd-dictator-affine-hull-no-go-proof.md),
now expressed in the variables on which the nested-conjugacy bridge acts.

## 5. What Theorem 5.5 can and cannot do

One may declare (5) as the ordinary BCS relation and then apply Theorem 5.5.
The theorem gives a quantitative embedding into another BCS algebra,
preserves the relevant tracial states, and converts the nested-conjugacy
scaffolding using Lemma 3.12.  That is a useful BCS-to-BCS reduction.

It does not derive (5) from the cell's group relations, and its proof does
not replace the retained ordinary BCS relation by parity equations.  If one
drops that relation in order to demand an LCS output, Section 4 supplies all
odd scalar characters again.  If one retains it, the output remains a
general BCS at precisely the place where the dictator selector lives.

Nor does iterating the Taller--Vidick test close the loop.  At positive
noise its support contains the previously isolated same-left-side,
opposite-right-side pair, so perfect completeness is lost.  At zero noise,
Section 2 returns the same abelian torsor and Section 4 returns its entire
odd affine hull.

Therefore arXiv:2510.04943 supplies no hidden perfect BCS-to-LCS bridge for
this route.  The residual gate is narrower: one needs a genuinely
non-scalar corner or compression which realizes the projections (5) as a
marked group relation and also has a reverse finite-dimensional decoder.
The argument here neither constructs such a corner nor rules one out.
