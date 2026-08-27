# A self-similarity phase seed beyond the perfect-overlap boundary

Date: 2026-08-11

> **Current status.** This note records the route to the first exact local
> phase.  Its active finite endpoint is superseded by
> `FALSE_ATLAS_DUAL_NUMBER_CENTRAL_QUOTIENT.md`, which kills all 24 certified
> zero classes and centralizes `s_11` in a finite full-chart image.  The
> current obstruction is the simultaneous four-survivor problem isolated in
> `FALSE_ATLAS_BOOLEAN_DUAL_NO_GO.md`; the historical solver directions below
> should not be read as the present research priority.

## 1. The first irreducible boundary relation

Retain the two scalar charts

\[
 C_1=(01,1,000,001),\qquad C_2=(00,1,010,011)
\]

inside the binary Leavitt unit group.  In \(GL_4(\mathbb F_2)\), put

\[
 a=I+E_{10},\qquad b=I+E_{01},\qquad
 c=I+E_{12},\qquad d=I+E_{01}+E_{12}=cb.              \tag{1}
\]

All of \(a,b,c\) are involutions and \(d\) has order four.  The first
all-depth survivor returned by
`experiments/atlas_perfect_overlap_scan.py` is

\[
 r=a_2b_1c_2b_1a_2b_1c_2d_1.                          \tag{2}
\]

It is an exact Leavitt relation.  Direct prefix multiplication gives

\[
 r=000(000)^*+001(001)^*+010(010)^*+011(011)^*+1(1)^*=1. \tag{3}
\]

Thus \(r\in R=\ker(A_8*A_8\to L_{\mathbb F_2}(1,2)^\times)\).
Its factor projections are

\[
 \operatorname{pr}_2(r)=1,\qquad
 \operatorname{pr}_1(r)=I+E_{02}+E_{12}.              \tag{4}
\]

Unlike the shorter Clifford word, `(2)` cannot be placed in one scalar leaf
chart.  Indeed, a scalar chart containing a transvection
\(1+\alpha\beta^*\) also contains its source and range cylinder projections:
multiply its nilpotent part by its adjoint in the chart matrix algebra.  The
chart must therefore refine both cylinders.

For the factor-two letters \(a,c\), equality of the descendant suffix codes
forces

\[
 \mathcal S_{00}=\mathcal S_1=\mathcal S_{010}.        \tag{5}
\]

For the factor-one letters \(b,d\), note that \(db=c\); hence the same chart
also contains the transvection \(c_1\).  It follows that

\[
 \mathcal S_{01}=\mathcal S_1=\mathcal S_{000}.       \tag{6}
\]

Equations `(5)--(6)` identify \(\mathcal S_{00}\) with
\(\mathcal S_{000}\).  This is impossible for a finite complete suffix
code: descendants of the \(000\)-cylinder occur inside the \(00\)-suffix
code with an additional leading zero, so the equality would imply

\[
 0\mathcal S_{00}\subseteq\mathcal S_{00}.            \tag{7}
\]

Iteration produces suffixes of unbounded length in a finite nonempty set.
This is the concrete self-similarity loop behind the cardinality obstruction
in `FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md`.

The conclusion is deliberately limited: no single scalar chart can fill
`(2)`.  A chain of intermediate perfect overlaps or another global relation
could still prove \(r\in[P,R]\).

## 2. Its local groups are \(D_8\) and \(V_4\)

The factor-one letters generate

\[
 H_1=\langle b,c\rangle\cong D_8,                     \tag{8}
\]

whereas the factor-two letters commute and generate

\[
 H_2=\langle a,c\rangle\cong V_4.                     \tag{9}
\]

There is an exact two-dimensional projective phase for `(2)`.  Let \(X,Y,Z\)
be the Pauli matrices and, for \(\theta\in\mathbb R\), put

\[
 A_\theta=\cos(\theta)X+\sin(\theta)Y.                \tag{10}
\]

Represent \(H_1\) by

\[
 b\longmapsto X,\qquad c\longmapsto Z,                \tag{11}
\]

and represent \(H_2\) by

\[
 a\longmapsto A_\theta,\qquad c\longmapsto A_\theta. \tag{12}
\]

The first assignment is the faithful two-dimensional irreducible
representation of \(D_8\); the second is the sum of the two \(V_4\)-characters
on which \(a\) and \(c\) have equal signs.  Direct Pauli multiplication gives

\[
 r\longmapsto i\sin(4\theta)I-\cos(4\theta)Z.          \tag{13}
\]

At \(\theta=\pi/8\), therefore,

\[
 r\longmapsto iI_2.                                   \tag{14}
\]

This is an honest representation of the local free product \(D_8*V_4\).
The phase is fourth-order, but it is attached to a relation which has already
passed the all-depth single-chart obstruction.

## 3. The phase block occurs inside two honest \(A_8\) charts

Let \(W\) be the 64-dimensional \(A_8\)-irrep obtained from the
\((5,2,1)\) Specht module.  Its character has

\[
 \chi_W(1)=64,\qquad \chi_W(2^4)=0,\qquad
 \chi_W(4^2)=0.                                      \tag{15}
\]

Let \(\tau\) denote the two-dimensional representation `(11)` of \(D_8\).
Its character is \(2\) at the identity, \(-2\) at the central involution,
and zero on the other six elements.  The central involution and the four
reflections are in the \(2^4\) class of \(A_8\), while the two order-four
elements are in the \(4^2\) class.  Hence

\[
 \langle\operatorname{Res}^{A_8}_{D_8}\chi_W,\chi_\tau\rangle
 ={1\over8}(2\cdot64-2\cdot0)=16.                    \tag{16}
\]

Every nonidentity element of the selected \(V_4\) is likewise in the
\(2^4\) class.  Character orthogonality therefore gives multiplicity
sixteen for each of its four characters in
\(\operatorname{Res}^{A_8}_{V_4}W\).  In particular, the two characters
used in `(12)` occur sixteen times each.

It follows that two honest copies of \(W\), one for each \(A_8\) chart, can
be relatively aligned so that a common 32-dimensional reducing subspace is
the direct sum of sixteen copies of `(11)--(12)`.  On that subspace `(14)`
holds exactly.

The complementary restrictions can also be aligned into one-dimensional
local blocks.  The four one-dimensional \(D_8\)-characters occur eight times
each; the two unused \(V_4\)-characters occur sixteen times each.  On this
complement the relation has eigenvalue \(+1\) on sixteen dimensions and
\(-1\) on sixteen dimensions.  Thus we obtain:

**Theorem (honest-chart self-similarity seed).**  There are honest
representations

\[
 \rho_1,\rho_2:A_8\longrightarrow U(64),
\]

both equivalent to \(W\), for which \(\rho(r)\) commutes with the local
subgroups \(H_1\) and \(H_2\) and has spectrum

\[
 i^{[32]},\qquad 1^{[16]},\qquad(-1)^{[16]}.           \tag{17}
\]

In particular,

\[
 \operatorname{tr}_{64}(\rho(r))={i\over2},\qquad
 \|\rho(r)-1\|_2^2=2.                                \tag{18}
\]

## 4. The 56 survivors reduce to four central classes

The eight tensor-flip projection classes are not the intrinsic quotient.
Classify the 56 survivor words inside the free product

\[
 P=A_{8,1}*A_{8,2}
\]

up to conjugacy and inversion. Exact free-product normal-form reduction
gives four classes, each containing fourteen of the 56 records. Their
smallest collision-tree indices are

\[
 11,\qquad 30,\qquad 44,\qquad 55.                  \tag{19}
\]

Every representative has cyclically reduced length eight. The full index
lists, with the six length-nine words marked by a superscript star, are

\[
\begin{aligned}
\mathcal C_{11}={}&\{11,23,27^*,28,29,33,34,84^*,161,171,172,181,182,183\},\\
\mathcal C_{30}={}&\{30,31,32,107,108,109,123,166,167,168^*,170,173,174,175\},\\
\mathcal C_{44}={}&\{44,48,52^*,53,54,66,67,118^*,136,146,147,197,198,199\},\\
\mathcal C_{55}={}&\{55,56,57,81,82,83,89,137,138,139^*,143,148,149,150\}.
                                                               \tag{20}
\end{aligned}
\]

This is an exact classification, not a bounded conjugator search. First
freely reduce a word. If its first and last syllables lie in the same free
factor, write it as \(xuy\), conjugate by \(x^{-1}\), and replace the two
end syllables by the single product \(yx\). Iteration gives a cyclically
reduced conjugate. The conjugacy theorem for free products says that two
cyclically reduced words of length at least two are conjugate precisely when
one syllable list is a cyclic rotation of the other. Comparing all rotations
of each reduced word and its inverse therefore decides the classification.
The matrix products and inverses are exact over \(\mathbb F _2\).

No representative in (19) is conjugate in \(P\) to its inverse. Thus this
calculation does not create a two-torsion relation among the four remaining
classes. It does, however, halve the live package. In the central kernel

\[
 R/[P,R],
\]

conjugate relators have equal classes and inversion negates a class. Hence
the entire first-boundary survivor package is generated, up to sign, by at
most the four classes in (19), not by eight independent projection types.

The exact calculation is reproduced by running
experiments/atlas_survivor_conjugacy.py on the JSON artifact generated by
the perfect-overlap scan documented in FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md.

## 5. The one-chart obstruction is conjugacy-saturated

Conjugating a relator before applying the perfect-overlap certificate cannot
remove the obstruction.  This is an all-length statement, not an exhaustive
search with a bounded conjugator.

First note a monotonicity property of the cardinality test.  The matrix
supports of a word generate an equivalence relation on the seven suffix-code
variables.  Adding more letters can only merge equivalence classes.  If one
of the two cardinality equations has coefficients of only one nonzero sign,
then every further merge still has coefficients of only that sign: merging
with a zero class changes nothing and merging two nonzero classes adds
coefficients of the same sign.  Hence a positive-cardinality obstruction,
once present, survives the addition of arbitrary letters.

Now let $c$ be cyclically reduced in a free product.  The standard
conjugacy normal form writes every reduced conjugate as

$$
u c' u^{-1},
$$

where $c'$ is a cyclic rotation of $c$.  Its support relations include all
support relations of $c'$, so the preceding monotonicity applies.

For each of the four representatives in `(19)`, exact arithmetic over
$\mathbb F _2$ checks all eight cyclic rotations of its length-eight core
and all eight rotations of the inverse.  Every one of these 64 oriented
cores obstructs both cardinality equations `(3)`.  We therefore obtain:

**Theorem (conjugacy-saturated one-chart obstruction).**  No conjugate in
$A_{8,1}*A_{8,2}$ of any of the 56 surviving relators, or of its inverse,
can have all its letters represented on one finite scalar leaf chart.
Consequently none can be killed by first changing its free-product basepoint
and then applying a single common-chart perfect-overlap certificate.

The exact check is reproduced by
`experiments/atlas_survivor_conjugacy_obstruction.py`.  An independent
exhaustion of all 40,320 conjugations by one chart element agrees with the
theorem: not one removes the sign obstruction.

## 6. The four classes have one abstract local type

The four classes remain distinct under inner conjugacy in the free product,
but their local finite-group patterns are equivalent.  In the matrix model

$$
\operatorname{Aut}(A_8)
=\operatorname{Inn}(A_8)\rtimes
\langle g\mapsto(g^{-1})^T\rangle,
$$

so all 40,320 automorphisms can be enumerated exactly.  Apply one such
automorphism independently in each free factor, allow interchange of the two
factors, and compare cyclic rotations of the word and its inverse.  The four
classes in `(19)` form one orbit under this action.

The concrete atlas symmetries identify half of them.  Let $v$ be the prefix
replacement which matches the ordered charts

$$
(01,1,000,001)\longleftrightarrow(00,1,010,011).
$$

It is an involution: it sends the second chart back to the first because
$00=000\sqcup001$ maps to $010\sqcup011=01$, while $010$ and $011$ map to
$000$ and $001$.  Consequently conjugation by $v$ swaps the two $A_8$
chart embeddings with the same matrix coordinate.  On the four oriented
classes it acts by

$$
11\longleftrightarrow55,
\qquad 30\longleftrightarrow44.
$$

This is an inner automorphism of the Leavitt group.  Its functorial lift to
the universal central cover is conjugation by a lift of $v$, hence acts
trivially on the central kernel.  Therefore

$$
[r_{11}]=[r_{55}],\qquad [r_{30}]=[r_{44}]
\quad\hbox{in }R/[P,R].
$$

Thus the 56-word boundary package is generated up to sign by at most two
central classes, not four.

There is a second genuine Leavitt symmetry.  The algebra involution induces
the group automorphism $u\mapsto(u^*)^{-1}$, whose restriction to every
scalar chart is the graph automorphism
$g\mapsto(g^{-1})^T$.  It exchanges classes $11\leftrightarrow44$ and
$30\leftrightarrow55$, again with positive orientation.  Hence it exchanges
the two remaining central generators.  It need not act trivially on the
central kernel, so this last symmetry does not identify them.

Arbitrary independent factor automorphisms likewise need not preserve the
concrete kernel $R$.  Their one-orbit calculation still shows that all four
have the same abstract $D_8*V_4$ local obstruction type.  Thus the character
and phase calculation in Sections 2--3 applies, after transport, to every
remaining class.

The exact orbit calculation is reproduced by
`experiments/atlas_survivor_automorphism_orbit.py`.

## 7. Exact scope

Theorem `(17)` is stronger than a representation of the small local groups:
both chart marginals are honest irreducible \(A_8\) representations, and the
phase occupies half their dimension.  It is also weaker than a representation
of the central atlas quotient.  Since the common 32-dimensional block is not
an \(A_8\)-invariant subspace, `(17)` does not make \(r\) commute with all of
either chart.  Nor does the absence of a common scalar chart prove that the
class of \(r\) is nonzero in \(R/[P,R]\).

The next exact gate is now sharply bounded: determine whether the two
central generators represented by the four all-depth survivor classes die
along genuinely multi-chart chains of perfect overlaps. Section 5 proves
that inserting a conjugating tail and returning to one common chart cannot
do this. Sections 9--10 solve the formerly conditional deformation gate:
the multiplicity alignment in `(17)` can be chosen
so that \(r\) centralizes the full two \(A_8\) charts without losing its
macroscopic spectrum. Only multi-relator survival remains at this stage.

## 8. Executable realization and the full-chart defect

`experiments/atlas_self_similarity_block.py` constructs the relative chart
unitary directly from the exact spectral projectors in \(W\).  There are six
ways to partition the four one-dimensional \(D_8\)-characters between the two
unused \(V_4\)-characters.  The script exhausts all six; there is no random
initialization and no optimization.

Every assignment reproduces `(17)--(18)` to less than
\(1.6\cdot 10^{-14}\):

\[
 \operatorname{spec}(\rho(r))
 =i^{[32]}\sqcup1^{[16]}\sqcup(-1)^{[16]},\qquad
 \operatorname{tr}_{64}(\rho(r))=i/2,
\]

and the maximum normalized Hilbert--Schmidt commutator defect against the
local \(D_8\) and \(V_4\) generators is below \(1.3\cdot10^{-14}\).  Thus the
character calculation and the Pauli block are realized inside the honest
charts exactly, up to floating-point diagonalization error.

The global diagnostic is also uniform across all six assignments:

\[
 \max_{x\in S_1\cup S_2}
 \|[\rho(r),\rho(x)]\|_2={5\over4},                 \tag{21}
\]

where \(S_j\) is the six standard transvection generators of chart \(j\).
For the two best complementary assignments the RMS defect over the twelve
generators is \(0.8228507358\).  In the first chart, the local generators
\(b=I+E_{01}\), \(c=I+E_{12}\), and \(I+E_{32}\) commute with \(\rho(r)\),
while the three exposed directions have defects \(1\), \(5/4\), and
\(\sqrt{3/2}\).  The obstruction is therefore not a numerical artifact or a
bad choice among the six discrete complement matchings.

This closes one tempting shortcut: the exact local phase block cannot simply
be repeated and declared a central microstate.  A live continuation must
deform the relative \(U(64)\) alignment so that the full-chart defect falls
while retaining a macroscopic nonidentity value of \(r\), or must couple
several copies nonorthogonally.  Orthogonal averaging cannot help because its
maximum defect is the maximum of its blocks.

## 9. Full relative-unitary continuation

The deformable gate in the preceding paragraph gives strong positive signal.
Starting from the lowest-RMS exact complement and varying the full relative
$U(64)$, a cyclic-gradient worst-tail continuation produced

\[
 \max_{x\in S_1\cup S_2}\|[\rho(r),\rho(x)]\|_2
 =0.0295801,
\]

while simultaneously moving

\[
 \operatorname{tr}_{64}(\rho(r))
 ={i\over2}
 \quad\hbox{to}\quad
 2.4\cdot10^{-9}+0.9998817i.                         \tag{22}
\]

In fact \(\|\rho(r)-iI\|_2=0.0153837\) and the operator-norm error is
$0.0423631$.  The retained relative unitary moved normalized-HS distance
$0.78677$ from the seed and is dense, so this is a genuinely global
alignment rather than a small correction of the Pauli block.

The live equation is now the exact finite-dimensional problem

\[
 \rho_U(r)=iI_{64}.                                  \tag{23}
\]

Solving `(23)` would certify an exact nontrivial phase after centralizing the
normal closure of this one relator.  It would not alone prove survival in
\(R/[P,R]\), since commutators with the other Leavitt relators may impose
additional identifications.  Numerics alone do not establish even `(23)`, and
the downstream negative central corner remains separate.  The full
continuation record and exact commands are in
`experiments/atlas_self_similarity_refine_results.md`.

Local L-BFGS and an independently implemented matrix-free Gauss--Newton solve
lower the retained error further to

\[
 \|\rho_U(r)-iI\|_2=1.11046\cdot10^{-4},\qquad
 \|\rho_U(r)-iI\|_{\rm op}=2.82906\cdot10^{-4}.     \tag{24}
\]

The tangent adjoint check passes at $1.2\cdot10^{-16}$, but every deep LSMR
solve hits its iteration cap, so numerical polishing is now
ill-conditioned. There is an exact simplification. With

\[
 A=\rho_U(a_2),\quad E=\rho_U(c_2),\quad
 B=\rho(b_1),\quad C=\rho(c_1),
\]

put $T=ABE$. Then

\[
 \rho_U(r)=iI
 \quad\Longleftrightarrow\quad
 (BT)^2=(BABE)^2=iC.                                \tag{25}
\]

Thus the next exact task is a finite square-root factorization: choose a
square root $Y$ of $iC$ and factor it as $Y=BABE$, where $A,E$ are commuting
involutions with four joint eigenspaces of dimension sixteen. Further blind
weight or seed searches are superseded by this spectral problem.

## 10. Exact solution of the square-root factorization

The factorization in `(25)` has an exact solution already in the minimal
8-dimensional multiplicity block. In the canonical basis $0,\ldots,7$, let
$B,C$ act as two copies of the faithful $D_8$ representation followed by its
four linear characters. Define

\[
 S=(0\ 7)(1\ 6)(2\ 5)(3\ 4),\qquad
 P=(0\ 6)(2\ 4)(3\ 5)(1\ 7),                       \tag{26}
\]

and

\[
 F={I+iC\over\sqrt2},\qquad A=BPB,\qquad E=PSF.    \tag{27}
\]

The permutation identities

\[
 P^2=S^2=1,\quad PC=-CP,\quad PS=SP,\quad SC=CS
\]

show that $E$ is a self-adjoint involution. Exact multiplication also gives

\[
 [A,E]=0,\qquad
 \operatorname{Tr}(A)=\operatorname{Tr}(E)
 =\operatorname{Tr}(AE)=0.                          \tag{28}
\]

Hence every joint $(A,E)$-eigenspace has dimension two, exactly the required
two regular copies of $V_4$. Moreover

\[
 BABE=PE=SF,\qquad (SF)^2=F^2=iC,                  \tag{29}
\]

and therefore

\[
 \rho(r)=iI_8.                                      \tag{30}
\]

All identities are checked exactly over $\mathbb Q(\zeta_8)$ by
`experiments/atlas_self_similarity_block8_exact.py`. The restriction
multiplicities in the 64-dimensional $A_8$ irrep are eight times this block,
so amplification gives two honest $A_8$ chart representations with
$\rho(r)=iI_{64}$ exactly. In particular the relation now centralizes the
full chart images, not only its local $D_8$ and $V_4$ subgroups.

This completes the one-relator phase construction. It does not alone prove
that the class of $r$ is nonzero in $R/[P,R]$, because the commutators with
all other Leavitt relators can impose additional relations. That
multi-relator central-kernel survival question is now the sole algebraic gate
for this witness before the downstream negative-corner problem.

## 11. All-depth obstruction to sequential scalar-prefix galleries

The one-chart obstruction from Section 5 does not by itself exclude changing
charts after every syllable.  There is, however, now an exact all-depth
obstruction to this larger strategy.

Fix an oriented cyclic representative

\[
 w=l_1\cdots l_8=1,
 \qquad q_j=l_1\cdots l_j.
\]

A scalar-prefix gallery would choose, at each step, a finite scalar leaf
chart containing both the running prefix $q_j$ and the next original syllable
$l_{j+1}$.  Perfect-overlap bridges between consecutive choices would then
identify the canonical lifts and kill the central class.  Thus it is enough
to prove that every orientation has at least one step at which no such scalar
chart exists.

For ten of the sixteen rotations and inverse-rotations of each of the two
central class representatives $r_{11}$ and $r_{30}$, the first two letters
already have the positive suffix-cardinality obstruction of Section 5.  The
remaining six orientations in each class admit the following uniform
certificate.  Put

\[
 D=(000,001,010,011,10,11).                         \tag{31}
\]

For a suitable $j\in\{2,3\}$, exact calculation in the binary Leavitt algebra
shows that the star-algebra generated by $q_j$ and $l_{j+1}$ contains all six
cylinder projections

\[
 p_d=dd^*,\qquad d\in D.                            \tag{32}
\]

This is a finite algebraic certificate: each $p_d$ is expressed as an
$\mathbb F _2$-linear combination of words in
$q_j,l_{j+1},q_j^*,l_{j+1}^*$ of length at most seven.  The executable audit
prints all identities and then substitutes them back into the Leavitt
relations exactly.

Suppose a finite scalar chart $C$ contained $q_j$ and $l_{j+1}$.  Its matrix
algebra is star-closed, so `(32)` puts every $p_d$ in that matrix algebra.  A
cylinder projection $p_d$ belongs to a scalar-chart matrix algebra only if
the chart refines the cylinder $d$.  Hence $C$ refines $D$.

Write $S_d$ for the nonempty finite suffix code below $d$ in $C$.  In every
one of the twelve remaining orientations, the support graph of $q_j$ on the
chart `(31)` has precisely the two components

\[
 \{000,010,10\},\qquad \{001,011,11\}.              \tag{33}
\]

Representation on $C$ therefore forces equality of the suffix codes within
each component.  Set their positive cardinalities equal to $x$ and $y$.
The support of the next letter then equates one $x$-sized descendant code
with a disjoint union of an $x$-sized and a $y$-sized code.  Concretely, the
ordinary cases give either

\[
 |S_{010}|=|0S_{10}\sqcup1S_{11}|
 \quad\hbox{or}\quad
 |S_{000}|=|0S_{10}\sqcup1S_{11}|,
\]

and the two exceptional support components give the same equation after
interchanging the relevant source leaf.  In all cases,

\[
 x=x+y,
\]

contradicting $y>0$.

We have therefore proved:

**Theorem (scalar-prefix-gallery no-go).**  For every cyclic rotation of
$r_{11}$ or $r_{30}$ and of its inverse, some original-syllable prefix
$q_j$ and next syllable $l_{j+1}$ do not lie together in any finite scalar
leaf chart.  Consequently neither of the two genuine radius-five central
classes can be killed by a sequential finite scalar-prefix gallery with
perfect-overlap transitions.

The exact certificate is reproduced by
`experiments/atlas_survivor_prefix_obstruction.py`; all 32 orientations are
covered, with 20 first-pair obstructions and 12 generated-projection
obstructions.  The bounded explorer
`experiments/atlas_survivor_prefix_gallery.py` independently agrees through
eight leaves.

The scope remains important.  This theorem rules out an entire all-depth
multi-chart method, but it does not prove either central class nonzero in
$R/[P,R]$.  A general two-dimensional disc diagram may use killed relators
in an order that is not a single running-prefix gallery, and non-scalar
perfect subgroups are not covered.  Those are now the live algebraic routes.

## 12. Complete radius-ten audit

The eightfold exact alignment has been evaluated on all 234 words in the
complete first boundary. Exactly fourteen are scalar: their indices are

\[
11,23,27,28,29,33,34,84,161,171,172,181,182,183,
\]

which is precisely the full conjugacy/inversion class $\mathcal C_{11}$.
They take values $\pm iI$ and have centrality defects below
$5.4\cdot10^{-15}$. None of the other 220 words is scalar; the next scalar
deviation is $0.99835$. In particular none of the 178 certified-zero words
maps to the identity. The maximum remaining centrality defect is
$1.7375382832$ and the boundary RMS is $1.4149416221$.

Therefore the exact construction is coherent on one entire central class but
does not factor through $P/[P,R]$. The next solver must impose the 24
certified-zero cyclic classes simultaneously while retaining the
$\mathcal C_{11}$ phase. Reproduction and full scope are in
`experiments/atlas_self_similarity_global_audit_results.md`.

## 13. Simultaneous 24-class compatibility experiment

The prescribed next finite solver has now been run.  The 178
perfect-overlap-certified zero words collapse to 24 cyclic classes.  Keeping
the two honest `A8` chart representations exact and varying only their relative
unitary, we minimized the mean squared identity defect of those 24 class
representatives together with a weighted `C11 -> iI` defect.

In dimension 64 the best phase-preserving continuation recorded zero-class RMS
`1.279437` at phase HS error `0.008520`.  A symmetry-broken search on two
copies in the full `U(128)` improved this only to zero-class RMS `1.271406` at
phase error `0.008401`.  The enlarged optimizer has substantial off-block
mass, so this is a genuine multiplicity coupling, but the improvement is only
`0.6%`.  Conversely, zero-only searches reached RMS about `0.65` while sending
the phase error to about `sqrt(2)`.  Two Haar restarts and continuation from
both ends reproduce the qualitative tradeoff.

This is not a lower bound or a disproof of the FALSE route.  It is a scoped
negative result for the fixed `(5,2,1)` vertex representations and one relative
intertwiner.  The persistent phase-preserving worst package consists of source
classes `70`, `86`, `90`, and `91`, but a subsequent exact finite quotient
shows that those four local relators do not force the phase to vanish: the
obstruction must use further certified classes or the extension from the local
`S4` subgroups to the full `A8` charts.  Full loss tables and multiplicity
checks are in `experiments/atlas_self_similarity_multirelator_results.md`; the
finite quotient is proved in `notes/FALSE_ATLAS_STUBBORN_S4_QUOTIENT.md`.

The finite quotient also supplies a better continuous endpoint.  On the
outer-stable representation
`rho directSum (rho after theta)` in dimension 128, the certified outer
alignment kills all 24 zero classes exactly.  Searching from a perturbed copy
shows that the involutory scalar target `-I` is far better than the original
`iI` target.  A retained point has zero-class RMS `0.352252`, zero maximum
`0.555910`, phase HS error `0.212666`, phase operator error `0.412192`, and
phase trace `-0.977386`.  At larger phase weight, phase HS drops to `0.057228`
and operator error to `0.115708`, while zero RMS is `0.491114`.

These are finite-dimensional signals only.  The next valid computation is
symmetry-broken multiplicity scaling of this outer-stable family; more
same-dimensional `iI` seeds are demoted.  Full data and the construction of
the exact-zero endpoint are in
`experiments/atlas_self_similarity_multirelator_results.md`.

Multiplicity two supplies no useful scaling.  A full `U(256)` continuation
from duplicated balanced states changes `(zero RMS, phase HS)` only from
`(0.352252,0.212666)` to `(0.352035,0.212209)`, a `0.205%` weighted-objective
improvement.  A ten-times larger symmetry break returns the same errors.
Stop duplicating this fixed outer pair; the next model must change its actual
`A8` irrep content.

The exact 30-dimensional outer tangent model has also been tested with the 12
phase commutators imposed explicitly.  Although its 24-zero tangent kernel has
dimension 136 and phase-moving rank 60, kernel-directed and random starts do
not centralize the phase: the best all-identity RMS is `0.480563`, the maximum
centrality constraint is `1.368373`, and phase HS remains `1.366428` at weight
one.  Generic full-unitary descent therefore does not integrate the tangent
signal.  This left tangent-kernel second-order equations and the order-2688
local block as the two candidate continuations at that stage.  The later
dual-number quotient supersedes the latter and the Boolean no-go sharpens the
former; do not launch more unrestricted 30-dimensional seeds.

## 14. Prefix replication cannot scale the local phase

There is now an exact homological restriction on every proposed scaling of
the finite blocks above.  The canonical prefix insertion

```text
kappa:Q->Q
```

induces the zero map on `H_2(Q,Z)`.  Its functorial lift to the universal
central extension therefore kills the whole central kernel.  Under
leaf-matrix self-similarity this is exactly transported standard matrix
stabilization.

Consequently, if one of the local scalar phases in this note represents a
genuine class of `R/[P,R]`, precomposing a full atlas representation with
prefix insertion sends that phase to the identity in one step.  Direct
sums, tensor products, or conjugates of such prefix-stabilized models do not
restore it.  The failure of the exact eight-dimensional block on the other
certified-zero relations is therefore load bearing: the phase cannot be
made into a full model merely by refining or repeating the same block down
the binary tree.

Any surviving higher-order route must change the actual cross-chart holonomy
or the `A8` representation content as the relation window grows.  The
order-2688 route has since been superseded by the complete certified
dual-number quotient.  Full proof:
`FALSE_PREFIX_TWISTED_SUBALGEBRA_RIGIDITY.md`.
