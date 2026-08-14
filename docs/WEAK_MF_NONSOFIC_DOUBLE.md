# An operator-MF nonsofic symmetric double: paper argument and formal reduction

## Status of Question 1.6 on sofic doubles

Gao--Kunnawalkam Elayavalli--Mj ask in Question 1.6 of *On soficity
for certain fundamental groups of graphs of groups* (arXiv:2408.11724):

> If (G) is a countable sofic group, are arbitrary doubles
> (G *_H G) sofic?

At the paper level, the Kun--Thom pair gives a negative answer: its ambient
group (G) is countable and residually finite, hence sofic, and the reduction
below implies

\[
G *_\Gamma G\quad\text{is nonsofic}.
\]

This paper-level conclusion follows by combining Kun--Thom's Theorem 4.1 with
Shulman's Theorem 10.  The repository proves internally the symmetric
amalgam, its flip, and the
presentation isomorphism

\[
G *_\Gamma(\Gamma\times C_2)
  \cong (G *_\Gamma G)\rtimes C_2,
\]

finite-semidirect-product permanence, and the embedding of the two-vertex
double into the infinite line double.  These are in
`GroupApproximation/Sofic/SoficFiniteSemidirect.lean`,
`GroupApproximation/Sofic/SymmetricDoubleFlip.lean`, and
`GroupApproximation/Sofic/LineDouble.lean`.

The remaining formal boundary is explicit rather than hidden.  The newer
centralizer-normalization theorem, the operator-MF conclusion, and the
construction of the concrete matrix-group pair have neither been reproved
from first principles nor instantiated as proof terms in the repository.
`GroupApproximation/Sofic/MFNonsoficDoubleEndpoint.lean` defines the exact
permutation-ultraproduct property
`HasSoficCentralizerNormalization`, proves the free-lamp and symmetric-double
nonsoficity arguments from it, and proves the conditional conjunction
`symmetricDouble_isGroupTheoreticMF_and_not_isSofic` from explicit hypotheses.
`KunThomShulmanDoubleData` is a proof-carrying interface for exactly those
hypotheses; the repository currently contains no concrete inhabitant of that
structure.  No opaque axiom is added to the project.

Given the centralizer-normalization and strict-compressor fields, the formal
reduction proves the load-bearing implication:

\[
\operatorname{Sofic}(G *_\Gamma G)
\Longrightarrow
\operatorname{Sofic}\bigl(G *_\Gamma(\Gamma\times C_2)\bigr)
\]

The endpoint theorem combines its contrapositive with an operator-MF
hypothesis supplied by its caller.  It does not construct the concrete
Kun--Thom elementary-group datum or discharge either recent literature input.
Those inputs are the stated boundary between the paper argument and the
conditional formal reduction.

The weak-MF conclusion discussed below is additional: nonsoficity alone gives
the negative answer to Question 1.6.

At the paper level, the resulting weak/operator-norm MF conclusion gives

\[
 \text{MF groups}\not\subseteq\text{sofic groups}.
\]

Thus the cited paper-level argument settles one inclusion in Andrew James
Schneider's broader Question 8
in his 2016 Purdue dissertation, *Finite dimensional approximations and
deformations of group C*-algebras*: “What is the relationship between the
class of MF groups, the class of sofic groups, and the class hyperlinear
groups?”  This is the appropriate narrow attribution; the dissertation does
not, on the evidence currently recorded, state the verbatim separately
numbered question “Is every MF group sofic?”  Here MF has Shulman's
operator-norm meaning, not the stronger property that has also appeared
under the same name.

This note repairs the group-level application of Shulman's symmetric
amalgamation theorem for the explicit Kun--Thom pair.  An arbitrary
weak-MF embedding of a group need not retain the abstract Bass--Serre normal
form after passing to the generated C*-algebra.  For a residually finite
group, however, the profinite regular embedding carries the regular group
trace, and that trace forces the required intersections to be exact.

Throughout, weak-MF means embeddability into

\[
 U\left(\prod_n M_{d_n}(\mathbb C)/\bigoplus_n M_{d_n}(\mathbb C)\right)
\]

with the quotient taken in operator norm.

## 1. The profinite regular completion remembers every subgroup

Let \(G\) be a countable residually finite group and let \(\Gamma<G\) be
arbitrary.  Choose a decreasing sequence of finite-index normal subgroups

\[
 G=N_0\geq N_1\geq N_2\geq\cdots,
 \qquad \bigcap_nN_n=\{1\},
\]

and put \(G_n=G/N_n\).  Let \(\lambda_n\) be the left regular
representation of \(G_n\), and define

\[
 \rho(g)=[(\lambda_n(gN_n))_n]
 \quad\text{in}\quad
 \prod_nM_{|G_n|}/\bigoplus_nM_{|G_n|}.
 \tag{1}
\]

The map \(\rho\) is injective.  Indeed, if \(g\neq1\), then \(gN_n\neq
N_n\) eventually.  For every nonidentity element \(x\) of a finite group,
the regular unitary \(\lambda(x)\) satisfies

\[
 \|\lambda(x)-1\|\geq \sqrt3.
\]

(For an element of order \(m\geq2\), maximize \(|\zeta-1|\) over the
\(m\)-th roots of unity.)

Let

\[
 A=C^*(\rho(G)),\qquad C=C^*(\rho(\Gamma))\subseteq A.
 \tag{2}
\]

An ultralimit of the normalized matrix traces defines a tracial state
\(\tau\) on \(A\).  The regular-character calculation gives

\[
 \tau(\rho(g))=\begin{cases}1,&g=1,\\0,&g\neq1.\end{cases}
 \tag{3}
\]

Consequently,

\[
 \boxed{\rho(g)\in C\quad\Longleftrightarrow\quad g\in\Gamma.}
 \tag{4}
\]

Only the reverse implication needs proof.  If \(g\notin\Gamma\), then for
every finite sum \(c=\sum_{\gamma\in F}a_\gamma\rho(\gamma)\),

\[
 \tau(\rho(g)^*c)=0
 \tag{5}
\]

by (3).  The same is true for every \(c\in C\) by norm continuity.  If
\(\rho(g)\) belonged to \(C\), taking \(c=\rho(g)\) in (5) would give
\(1=0\).

The argument proves a little more: in the GNS Hilbert space of \(\tau\),
\(\rho(g)\) is orthogonal to \(C\) whenever \(g\notin\Gamma\).  This remains
true even if \(g\) lies in the relative profinite closure of \(\Gamma\), so
finite-quotient collapse does not collapse the *fixed* C*-subalgebra \(C\).

## 2. Symmetric doubles of residually finite groups are weak-MF

The algebra \(A\) in (2) is separable and MF: it is a C*-subalgebra of the
norm matrix ultraproduct in (1).  Shulman's Theorem 10 therefore gives

\[
 B:=A*_C A\quad\text{is MF}.                             \tag{6}
\]

Let \(i_1,i_2:A\to B\) be the two canonical embeddings.  Define

\[
 \iota:G*_\Gamma G\longrightarrow U(B)
 \tag{7}
\]

by \(\iota(g)=i_1(\rho(g))\) on the first vertex group and
\(\iota(g)=i_2(\rho(g))\) on the second.

**Theorem.**  The map (7) is injective.  Hence every symmetric double of a
countable residually finite group over an arbitrary subgroup is weak-MF.

**Proof.**  Let \((\pi_\tau,H_\tau)\) be the GNS representation associated
to \(\tau\).  Equation (3) says that the representation
\(\pi_\tau\circ\rho\) is the left regular representation of \(G\).  Thus

\[
 \pi_\tau(A)''=L(G),\qquad \pi_\tau(C)''=L(\Gamma).
 \tag{8}
\]

Form the reduced tracial amalgam

\[
 M=L(G)*_{L(\Gamma)}L(G).
\]

The two copies of \(\pi_\tau:A\to L(G)\subset M\) agree on \(C\).
Universality of the full amalgam therefore gives a unital *-homomorphism

\[
 \Pi:B=A*_C A\longrightarrow M.
 \tag{9}
\]

The standard group-von-Neumann-algebra identification gives

\[
 M\cong L(G*_\Gamma G),
 \tag{10}
\]

and under this identification \(\Pi\circ\iota\) is the canonical left
regular representation of \(G*_\Gamma G\).  It is faithful as a group
representation: a nonidentity Bass--Serre reduced word has canonical trace
zero and hence is not the identity.  Therefore \(\iota\) itself is
injective.  Since \(B\) is MF, its countable unitary subgroup
\(\iota(G *_\Gamma G)\) is weak-MF. \(\square\)

The trace argument is the missing hypothesis in the invalid general
inference from an arbitrary weak-MF embedding.  For example, a faithful
irrational scalar representation of \(\mathbb Z\) generates only
\(\mathbb C\), and therefore folds the double over \(2\mathbb Z\).  The
profinite regular completion cannot fold in this way because (3) also
provides the detecting quotient (9)--(10).

The same proof and Shulman's finite-many-factors lemma give a useful
strengthening.  For every finite \(r\geq2\),

\[
 \underbrace{G *_\Gamma G *_\Gamma\cdots *_\Gamma G}_{r\text{ copies}}
 \quad\text{is weak-MF}.                               \tag{11}
\]

Indeed, the C*-algebra obtained by amalgamating \(r\) copies of \(A\) over
the same \(C\) is MF, and its GNS-detecting quotient is the corresponding
reduced von Neumann amalgam, namely the group von Neumann algebra of the
iterated group amalgam.

We will also use the elementary fact that weak-MF is closed under finite
extensions.  If \(N\triangleleft H\) has finite index \(r\) and
\(N\hookrightarrow U(A)\) with \(A\) MF, choose coset representatives for
\(H/N\).  The usual induced-representation matrices give an injective
homomorphism

\[
 H\longrightarrow U(M_r(A)).
\]

The entries are the images of the associated \(N\)-valued Schreier
cocycles.  A nonidentity element either moves a coset or has a nonidentity
diagonal cocycle entry, so the induced homomorphism is injective.  Since
matrix amplifications of MF algebras are MF, \(H\) is weak-MF.

## 3. Application to the Kun--Thom pair

This section gives the pen-and-paper consequence of the cited Kun--Thom
inputs.  The repository contains the abstract centralizer argument and the
final symmetric-double implication only in conditional form.  Applying that
formal implication to the concrete pair still requires an inhabitant of
`KunThomShulmanDoubleData`; none is currently defined.

Let \(\Gamma<G\) be the explicit residually finite Kazhdan infranormal pair
of Kun--Thom.  Choose a strict compressor \(t\) and
\(\gamma\in\Gamma\) such that

\[
 h=t^{-1}\gamma t\notin\Gamma.                          \tag{12}
\]

Put

\[
 D=G*_\Gamma G.
\]

The theorem above proves that \(D\) is weak-MF.  We next recall why it is
nonsofic, keeping track of the one word that must survive.

The flip of the two free factors defines an automorphism \(\alpha\) of
\(D\).  Let

\[
 E=D\rtimes_\alpha C_2,
\]

and write \(k\) for the flip generator.  Thus \(k^2=1\), \(k\) centralizes
the common copy of \(\Gamma\), and conjugates the first copy of \(G\) onto
the second.  The Kun--Thom witness is

\[
 w=[tkt^{-1},\gamma]
   =t[k,h]t^{-1}.                                      \tag{13}
\]

Abstract Bass--Serre normal form gives \([k,h]\neq1\) because
\(h\notin\Gamma\).  Hence \(w\neq1\) in \(E\).

If \(E\) were sofic, restrict a sofic embedding to the first copy of
\(G\).  Kun--Thom's centralizer-normalization theorem says that the
permutation-ultraproduct centralizer of the image of \(\Gamma\) is
normalized by the image of \(G\).  Since \(k\) centralizes \(\Gamma\), so
does \(tkt^{-1}\).  It would follow that the nontrivial word \(w\) in (13)
maps to the identity, contradicting injectivity.  Therefore \(E\) is
nonsofic.

Finally, if \(D\) were sofic, its extension by the finite quotient \(C_2\)
would be sofic.  Thus \(E\) would be sofic, a contradiction.  Using the cited
theorem, the argument proves:

\[
 \boxed{D=G*_\Gamma G\text{ is weak-MF and nonsofic}.}  \tag{14}
\]

There is a finite-lamp family version.  Let \(K\neq1\) be finite and put

\[
 H_K=G *_\Gamma(\Gamma\times K).
\]

The retraction \(H_K\to K\), trivial on \(G\) and equal to the second
coordinate on \(\Gamma\times K\), has kernel

\[
 \ker(H_K\to K)
 \cong \underbrace{G *_\Gamma\cdots *_\Gamma G}_{|K|\text{ copies}}.
 \tag{15}
\]

This is the Bass--Serre covering with one central \(\Gamma\)-vertex and
\(|K|\) outer \(G\)-vertices.  Its kernel is weak-MF by (11), and \(H_K\)
is weak-MF by finite-extension closure.  The same cited Kun--Thom
centralizer-normalization argument, using any \(1\neq k\in K\), proves
\(H_K\) nonsofic.  Using the same published input,

\[
 \boxed{
   K\neq1\text{ finite}
   \quad\Longrightarrow\quad
   G *_\Gamma(\Gamma\times K)
   \text{ is weak-MF and nonsofic}.
 }                                                       \tag{16}
\]

## 4. The forced exotic MF corner

At the paper level, the weak-MF statement makes the following operator-norm
localization theorem unconditional.  Let
\(H_K=G *_\Gamma(\Gamma\times K)\) be one of the groups above and let

\[
 \varphi:H_K\longrightarrow U(F)
\]

be an injective homomorphism into a unital finite C*-algebra \(F\).  This
includes the faithful realization in an MF norm ultraproduct constructed in
the paper argument above.  Let \(p_\Gamma\in C^*_{\max}(\Gamma)\) be the Kazhdan
projection and set

\[
 p=\varphi(p_\Gamma),\qquad q=1-p.
\]

Here the integrated representation is understood; the canonical map
\(C^*_{\max}(\Gamma)\to C^*_{\max}(H_K)\) is injective by induction of
representations.

**Proposition (forced exotic corner).**  The projection \(q\) commutes with
\(\varphi(H_K)\).  Fix \(1\neq k\in K\), retain \(t,\gamma\) from (12),
and put

\[
 w_k=[tkt^{-1},\gamma]\neq1.
\]

Then

\[
 p(\varphi(w_k)-1)=0,
 \qquad
 q(\varphi(w_k)-1)\neq0.                               \tag{17}
\]

In particular \(q\neq0\), and the unital corner \(qFq\) is a finite
C*-algebra carrying an operator-norm-visible image of the nonsofic witness
and no \(\Gamma\)-fixed summand.

**Proof.**  For a strict compressor \(s\), put \(U=\varphi(s)\).  In every
unitary representation, \(U^{-1}\) sends \(\Gamma\)-fixed vectors to
\(\Gamma\)-fixed vectors because \(s\Gamma s^{-1}\leq\Gamma\).  Hence

\[
 UqU^*\leq q.
\]

The two projections are unitarily equivalent.  Finiteness of \(F\) forbids
a projection from being equivalent to a proper subprojection, so equality
holds.  The compressor semigroup generates \(G\), and therefore \(q\)
commutes with \(\varphi(G)\).  Every element of the lamp copy \(K\)
centralizes \(\Gamma\), hence commutes with its Kazhdan projection and with
\(q\).  These elements generate \(H_K\), proving centrality.

On the \(p\)-corner, \(\Gamma\) acts trivially; since \(p\) also reduces the
whole representation, the commutator witness acts trivially there.  This is
the first equality in (17).  Bass--Serre normal form gives \(w_k\neq1\), and
injectivity of \(\varphi\) gives \(\varphi(w_k)\neq1\).  Centrality of
\(p,q\) and the first equality force all remaining deviation into the
\(q\)-corner, proving the second. \(\square\)

This is stronger than merely knowing that some MF embedding separates
\(w\): the location of every possible separation is canonical.  It still
does not give normalized-Hilbert--Schmidt mass.  Finite-stage lifts of \(q\)
may have growing rank while \(q(\varphi(w)-1)\) remains visible on only a
vanishing fraction of that rank.  Thus the exact unresolved analytic step
is now internal to \(qFq\): produce one Connes-embeddable corner trace which
does not annihilate the positive element

\[
 q(\varphi(w_k)-1)^*(\varphi(w_k)-1)q.
 \tag{18}
\]

This is a genuine separation of weak/operator-norm MF from soficity.  It
does **not** yet separate hyperlinearity from soficity: Shulman's MF
embedding supplies operator-norm separation, but its normalized traces need
not retain the fold-kernel witness (13).  The remaining main-problem
certificate is a trace-visibility theorem for this particular profinite
regular amalgam, or a pointwise square-root profile for Shulman's lifts.

## Sources

* Tatiana Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564v2, Theorem 10.
* G. Kun and A. Thom, *Nonsofic wreath products of residually finite
  groups*, arXiv:2608.06222v1, Theorem 4.1.
* K. Gao, S. Kunnawalkam Elayavalli, and M. Mj, *On soficity for certain
  fundamental groups of graphs of groups*, arXiv:2408.11724, Question 1.6.

The reduced-amalgamation paper *Selfless C*-correspondences, operator valued
C*-probability spaces and completely positive maps* is arXiv:2607.20361.  It
is a separate source and is not the source of Shulman's full symmetric-
amalgamation theorem.
