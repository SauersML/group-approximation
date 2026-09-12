# The Clifford atlas phase is a bounded central-kernel class

Date: 2026-08-11

## 1. Setup

Retain the two-chart notation of
`notes/FALSE_LOCAL_CLIFFORD_ATLAS.md`:

\[
 P=A_8*A_8,\qquad R=\ker(P\twoheadrightarrow Q),\qquad
 U=P/[P,R].
\]

There are involutions \(p_0,p_1,p_2\in P\) for which

\[
 q=p_1p_2p_0\in R.                                      \tag{1}
\]

The images of the \(p_i\) commute in \(Q\).  Thus the three commutators

\[
 c_{ij}=[p_i,p_j]\in R \qquad (0\leq i<j\leq2)          \tag{2}
\]

are central in \(U\), as is \(q\).  This note extracts the exact algebraic
content of those facts.  It deliberately makes no claim that the image of
\(q\) in \(U\) is nontrivial.

## 2. A class-two involution calculation

We use \([x,y]=xyx^{-1}y^{-1}\).

**Lemma 1.**  Let \(a,b\) be involutions in a group.  If \([a,b]\) is
central, then

\[
 [a,b]^2=1.                                             \tag{3}
\]

**Proof.**  Conjugation by \(a\) sends \([a,b]\) to \([b,a]=[a,b]^{-1}\).
Centrality says that the same conjugation fixes \([a,b]\).  Hence the
commutator equals its inverse.  End proof.

**Lemma 2.**  Let \(a,b,c\) be involutions whose three pairwise commutators
are central.  Then

\[
 (abc)^2=[c,a][b,a][b,c].                              \tag{4}
\]

In particular, \((abc)^4=1\).

**Proof.**  Lemma 1 makes every pairwise commutator an involution, so its
orientation is immaterial.  Moving the second \(a\) to the left in
\(abcabc\), using \(xy=[x,y]yx\), gives

\[
 abcabc=[c,a][b,a]bc bc=[c,a][b,a][b,c].
\]

The right side is a product of commuting involutions, so its square is one.
End proof.

**Lemma 3.**  Under the hypotheses of Lemma 2, if \(abc\) is central, then
the three pairwise commutators are equal.  Writing their common value as
\(d\), one has

\[
 (abc)^2=d.                                             \tag{5}
\]

**Proof.**  Centrality of \(abc\), together with centrality of the pairwise
commutators, gives

\[
 1=[abc,a]=[c,a][b,a].                                 \tag{6}
\]

Both factors are involutions by Lemma 1, so \([c,a]=[b,a]\).  Commuting with
\(b\), or cyclically repeating the same calculation, shows that this also
equals \([b,c]\).  Formula `(4)` is therefore the product of three copies of
the same involution \(d\), which equals \(d\).  End proof.

Applying the lemmas in \(U\) gives the following finite relation package.

**Theorem 4 (cyclic Clifford kernel).**  In \(U=P/[P,R]\), all three
pairwise commutators have a common value \(c\), and

\[
 c_{01}=c_{02}=c_{12}=c,\qquad
 c^2=1,\qquad q^2=c,\qquad q^4=1.                    \tag{7}
\]

Consequently the whole displayed central subgroup is cyclic:

\[
 C_{\rm Cl}=\langle q,c_{01},c_{02},c_{12}\rangle
             =\langle q\rangle,                         \tag{8}
\]

and has order at most four.

In additive notation inside the central kernel, the corresponding classes in

\[
 R/[P,R]                                                \tag{9}
\]

satisfy

\[
 [c_{01}]=[c_{02}]=[c_{12}]=2[q],\qquad 4[q]=0.       \tag{10}
\]

**Proof.**  All displayed elements are central because they belong to \(R\).
Apply Lemmas 1 and 3 with \((a,b,c)=(p_1,p_2,p_0)\).  This gives `(7)` and
`(8)`.  Writing the identities additively inside the central kernel gives
`(10)`.  End proof.

The group in `(9)` must not be identified with the whole Schur multiplier.
The five-term homology sequence gives

\[
 H_2(P,\mathbb Z)\longrightarrow H_2(Q,\mathbb Z)
 \longrightarrow R/[P,R]\longrightarrow0.            \tag{11}
\]

Here

\[
 H_2(P,\mathbb Z)
 \cong H_2(A_8,\mathbb Z)\oplus H_2(A_8,\mathbb Z)
 \cong C_2\oplus C_2,                                 \tag{12}
\]

so `P` is perfect but not superperfect.  GAP's exact
`AbelianInvariantsMultiplier(AlternatingGroup(8))` returns `[2]`, agreeing
with the standard multiplier calculation.  Thus `R/[P,R]` is a quotient of
`H_2(Q,Z)` after the two factor-multiplier classes are accounted for; it is
not canonically equal to `H_2(Q,Z)`.  The cyclic calculation `(7)--(10)` is
unchanged because it takes place directly in `R/[P,R]`.

## 3. The local Pauli block detects the universal bounded package

Let \(U_{\rm loc}\) be the quotient of \(P\) obtained by imposing only the
centrality of \(q\) and of the three \(c_{ij}\).  The exact Pauli block from
`FALSE_LOCAL_CLIFFORD_ATLAS.md` factors through \(U_{\rm loc}\) and has

\[
 q\longmapsto-iI,\qquad c_{ij}\longmapsto-I.           \tag{13}
\]

Equation `(7)` is visible numerically without approximation:

\[
 (-iI)^2=-I=(-I)^3.                                   \tag{14}
\]

Consequently \(q\) has exact order four in \(U_{\rm loc}\).  The later
atlas relations can only send this order-four class to an element of order
four, two, or one in the full quotient \(U\).  This separates two questions
which were previously bundled together:

1. **algebraic survival:** determine the image of \([q]\) in the central
   kernel \(R/[P,R]\);
2. **analytic survival:** construct exact representations of \(P\) in which
   a finite normal generating set of \([P,R]\) tends to one in normalized
   Hilbert--Schmidt norm while the \(q\)-phase stays nontrivial.

The first question is finite-primary: the class of `q` in the central kernel
has order dividing four, and any lift through `(11)` lies in the
two-primary multiplier quotient.  The next section reduces it further to a
single order-two lift discrepancy.

## 4. A common six-leaf chart kills the square of the phase

The local elements admit a common scalar refinement.  Put

\[
 D=(000,001,010,011,10,11).                            \tag{15}
\]

This is a complete binary prefix code.  In the first original chart, refine
the two active leaves \(01,1\) simultaneously:

\[
 01\rightsquigarrow010,011,qquad
 1\rightsquigarrow10,11.                              \tag{16}
\]

The matrices \(s,t\) then act as two identical copies of their active
two-dimensional matrices and fix \(000,001\).  In the second chart, refine
the two active leaves \(00,1\) simultaneously:

\[
 00\rightsquigarrow000,001,qquad
 1\rightsquigarrow10,11.                              \tag{17}
\]

The matrix \(b\) likewise acts by two identical active blocks and fixes
\(010,011\).  Hence all three elements belong to the one scalar chart

\[
 G_D\cong GL_6(\mathbb F_2)\leq Q.                    \tag{18}
\]

The standard Schur-multiplier calculation gives

\[
 H_1(G_D,\mathbb Z)=H_2(G_D,\mathbb Z)=0;             \tag{19}
\]

there is no low-rank exception for \(PSL_6(2)=GL_6(2)\).  Therefore the
pullback of the central extension \(U\to Q\) to \(G_D\) has a unique
splitting

\[
 \sigma:G_D\longrightarrow U.                         \tag{20}
\]

**Theorem 5 (the global Clifford class is an involution).**  In the full
cover \(U=P/[P,R]\),

\[
 c_{01}=c_{02}=c_{12}=1,qquad q^2=1.                 \tag{21}
\]

More precisely, let \(j:P\to U\) be the canonical map.  The two lifts of the
cyclic subgroup \(\langle b\rangle\cong C_2\), namely \(j\) from the second
original chart and \(\sigma\) from the common chart, differ by a character

\[
 \beta:C_2\longrightarrow Z(U),                       \tag{22}
\]

and

\[
 q=\beta(b).                                           \tag{23}
\]

Consequently the sole remaining algebraic question is whether this one
central sign is trivial.

**Proof.**  Two homomorphic lifts of the same subgroup into a central
extension differ by a homomorphism to the central kernel.  Therefore there
are characters \(\alpha:\langle s,t\rangle\to Z(U)\) and \(\beta\) as in
`(22)` such that

\[
 j(h)=\alpha(h)\sigma(h)\quad(h\in\langle s,t\rangle),
 \qquad j(b)=\beta(b)\sigma(b).                        \tag{24}
\]

The central factors \(\alpha(h)\) cancel when \(h\) conjugates \(b\), while
the same factor \(\beta(b)\) remains in each conjugate.  Hence

\[
 j(p_i)=\beta(b)\sigma(p_i)\qquad(i=0,1,2).            \tag{25}
\]

Inside \(G_D\), the three \(p_i\) commute and have product one: they are the
same exact Leavitt elements as in `(1)`, and the scalar-chart embedding is
injective.  Their images under \(\sigma\) therefore commute and have product
one.  Equation `(25)` makes every \(c_{ij}\) trivial and gives

\[
 q=\beta(b)^3=\beta(b).
\]

Finally \(\beta(b)^2=1\), because \(b^2=1\) and \(\beta\) is a character.
This proves `(21)--(23)`.  End proof.

Theorem 5 identifies a concrete later relation which obstructs the pure
Pauli block: the local value \(c_{ij}=-1\) must be driven to \(+1\) in every
full atlas approximation.  A global optimizer should therefore not preserve
the order-four phase \(q=-i\) as its target.  The only possible surviving
central witness from this cluster is the order-two phase \(q=-1\).  The next
section shows that even this sign vanishes.

## 5. A perfect overlap kills the residual sign

Uniformly refine every leaf of the second original chart

\[
 C_2=(00,1,010,011)
\]

by one binary digit.  The resulting complete code is

\[
 E=(000,001,10,11,0100,0101,0110,0111),              \tag{26}
\]

up to an irrelevant reordering, and gives a scalar chart

\[
 G_E\cong GL_8(\mathbb F_2).                           \tag{27}
\]

This group is superperfect.  Let

\[
 \tau:G_E\longrightarrow U                            \tag{28}
\]

be the unique splitting of the pullback of \(U\to Q\).  The original
second-chart lift \(j|_{K_2}\) and \(\tau|_{K_2}\) differ by a character
of \(K_2\cong A_8\) into the central kernel.  Since \(A_8\) is perfect,
that character is trivial.  In particular,

\[
 j(b)=\tau(b).                                         \tag{29}
\]

Now compare the two refined charts \(G_D\) and \(G_E\).  They have the four
literal common leaves

\[
 000,\quad001,\quad10,\quad11.
\]

The scalar transformations supported on these four leaves and fixing all
other leaves form one and the same subgroup of \(Q\) in both charts:

\[
 H=GL(\{000,001,10,11\},\mathbb F_2)
   \cong GL_4(\mathbb F_2)\cong A_8.                  \tag{30}
\]

Here ``fixing all other leaves'' means fixing \(010,011\) in the
six-leaf chart and fixing \(0100,0101,0110,0111\) in the eight-leaf chart.
The two descriptions give the same Leavitt units because the latter four
leaves refine the former two fixed cylinders.

The refined element \(b\) belongs to \(H\): on the four displayed leaves it
is the direct sum of the two identical active transvections, pairing
\(000\) with \(10\) and \(001\) with \(11\), and it fixes the complementary
cylinders.  The restrictions \(\sigma|_H\) and \(\tau|_H\) are two lifts of
the same inclusion \(H\hookrightarrow Q\).  Their quotient is a character
of the perfect group \(H\cong A_8\) into the central kernel, so it is
trivial.  Thus

\[
 \tau(b)=\sigma(b).                                    \tag{31}
\]

Combining `(23)`, `(29)`, and `(31)` gives the final calculation.

**Theorem 6 (the Clifford atlas word dies globally).**  In the full central
atlas quotient \(U=P/[P,R]\),

\[
 q=1,
 \qquad c_{01}=c_{02}=c_{12}=1.                       \tag{32}
\]

Equivalently, the explicit word \(q\) belongs to \([P,R]\), not merely to
\(R\).  Hence neither the order-four Pauli phase nor its residual order-two
sign can be a central survivor for the FALSE lane.

**Proof.**  Equations `(29)` and `(31)` give
\(j(b)=\sigma(b)\), so the discrepancy character in `(22)` satisfies
\(\beta(b)=1\).  Equation `(23)` gives \(q=1\).  The commutators were already
shown trivial in `(21)`.  End proof.

This argument uses only two uniqueness principles.  A superperfect scalar
chart has a unique lift to any central extension, and two lifts agree on a
perfect overlap.  It does not compute the rest of \(R/[P,R]\).  It does,
however, close the exact algebraic gate raised by the local Clifford block:
further numerical optimization of that block cannot retain any nontrivial
central phase after the full atlas relations are imposed.

## 6. What a different surviving atlas word would have to provide

The quotient \(Q\) is simple and nonsofic, and \(U\) is perfect with central
quotient \(Q\).  No claim about \(\operatorname{Rad}_{\rm sof}(U)\) is
available here: whether soficity passes to central quotients is itself open.
The required permanence theorem is instead Thom's theorem that a central
quotient of a hyperlinear group is hyperlinear.

For a different word \(z\in R\) whose class in \(R/[P,R]\) is proved
nontrivial, exact finite-dimensional representations
\(\pi_n:P\to U(d_n)\) satisfying

\[
 \|\pi_n(s)-1\|_2\longrightarrow0
 \quad(s\in\mathcal S),\qquad
 \liminf_n\|\pi_n(z)-1\|_2>0                         \tag{33}
\]

where the finite set \(\mathcal S\) normally generates \([P,R]\).  The
tracial ultraproduct homomorphism then factors through \(U\) and retains
\(q\).  Write \(K\) for its kernel.  Then \(K\) is a proper normal subgroup
of \(U\).  Its image in the simple quotient \(Q\) is either trivial or all of
\(Q\).  The latter is impossible: it would give \(U=KZ(U)\), and perfectness
would imply

\[
 U=[U,U]=[K,K]\subseteq K.
\]

Hence \(K\subseteq Z(U)\).  The hyperlinear image \(U/K\) is a central
cover of \(Q\), so Thom's hyperlinear central-quotient permanence makes
\(Q\) hyperlinear.  Since \(Q\) is already known to be nonsofic, this solves
the main problem negatively.  This is exactly the finite one-survivor
certificate already proved in `notes/ATLAS_HS_CRITERION.md`, now with a
bounded central witness.

The local Clifford certificate cannot supply `(33)`: Theorem 6 proves its
candidate survivor is already the identity in \(U\).  A viable replacement
must therefore come from a genuinely different cross-chart relation, first
survive the perfect-overlap test above, and only then be subjected to an
analytic atlas approximation search.
