# A self-similarity phase seed beyond the perfect-overlap boundary

Date: 2026-08-11

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
 \operatorname{pr}_2(r)=1,qquad
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
along genuinely multi-chart chains of perfect overlaps.  Section 5 proves
that inserting a
conjugating tail and returning to one common chart cannot do this.  If `(2)`
survives the multi-chart gate, deform the multiplicity alignment in `(17)`
so that \(r\) centralizes the full two \(A_8\) charts without losing its
macroscopic spectrum.  This is the first phase seed not already ruled out by
one-chart refinement.

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
