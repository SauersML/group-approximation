# The Clifford atlas phase is a bounded Schur-multiplier class

Date: 2026-08-11

## 1. Setup

Retain the two-chart notation of
`docs/FALSE_LOCAL_CLIFFORD_ATLAS.md`:

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

Applying the lemmas in \(U\) gives the following finite relation package.

**Theorem 3 (bounded Clifford kernel).**  In \(U=P/[P,R]\),

\[
 c_{ij}^2=1,\qquad
 q^2=c_{02}c_{12}c_{01},\qquad q^4=1,                 \tag{5}
\]

where the order of the three central factors in the middle identity is
irrelevant.  The central subgroup

\[
 C_{\rm Cl}=\langle q,c_{01},c_{02},c_{12}\rangle       \tag{6}
\]

is finite of order at most \(16\).  More precisely, the middle identity in
`(5)` eliminates any one of the three \(c_{ij}\), so \(C_{\rm Cl}\) is a
quotient of \(C_4\times C_2\times C_2\).

In additive Schur-multiplier notation, the corresponding classes in

\[
 R/[P,R]\cong H_2(Q,\mathbb Z)                         \tag{7}
\]

satisfy

\[
 2[c_{ij}]=0,\qquad
 2[q]=[c_{01}]+[c_{02}]+[c_{12}],\qquad 4[q]=0.        \tag{8}
\]

**Proof.**  Equations `(5)` are Lemmas 1 and 2 with
\((a,b,c)=(p_1,p_2,p_0)\).  All displayed elements are central because they
belong to \(R\).  Thus `(6)` is abelian, and `(5)` gives the asserted finite
presentation bound.  Abelianizing the same identities inside the central
kernel gives `(8)`.  End proof.

## 3. The local Pauli block detects the universal bounded package

Let \(U_{\rm loc}\) be the quotient of \(P\) obtained by imposing only the
centrality of \(q\) and of the three \(c_{ij}\).  The exact Pauli block from
`FALSE_LOCAL_CLIFFORD_ATLAS.md` factors through \(U_{\rm loc}\) and has

\[
 q\longmapsto-iI,\qquad c_{ij}\longmapsto-I.           \tag{9}
\]

Equation `(5)` is visible numerically without approximation:

\[
 (-iI)^2=-I=(-I)^3.                                   \tag{10}
\]

Consequently \(q\) has exact order four in \(U_{\rm loc}\).  The later
atlas relations can only send this order-four class to an element of order
four, two, or one in the full quotient \(U\).  This separates two questions
which were previously bundled together:

1. **algebraic survival:** determine the image of \([q]\) in the full
   multiplier \(H_2(Q,\mathbb Z)\);
2. **analytic survival:** construct exact representations of \(P\) in which
   a finite normal generating set of \([P,R]\) tends to one in normalized
   Hilbert--Schmidt norm while the \(q\)-phase stays nontrivial.

The first question is finite-primary: only the two-primary part of the
unstable Schur multiplier can contain \([q]\).  In particular, computations
or structural theorems about odd-primary multiplier classes are irrelevant
to this Clifford branch.

## 4. Why survival plus atlas approximation would finish the FALSE lane

The quotient \(Q\) is simple and nonsofic, and \(U\) is perfect with central
quotient \(Q\).  No claim about \(\operatorname{Rad}_{\rm sof}(U)\) is
available here: whether soficity passes to central quotients is itself open.
The required permanence theorem is instead Thom's theorem that a central
quotient of a hyperlinear group is hyperlinear.

Suppose now that \([q]\ne0\) in `(7)` and that exact finite-dimensional
representations \(\pi_n:P\to U(d_n)\) satisfy

\[
 \|\pi_n(s)-1\|_2\longrightarrow0
 \quad(s\in\mathcal S),\qquad
 \liminf_n\|\pi_n(q)-1\|_2>0,                        \tag{12}
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
certificate already proved in `docs/ATLAS_HS_CRITERION.md`, now with a
bounded central witness.

The local Clifford certificate proves neither hypothesis in the preceding
paragraph.  It proves instead that the first exposed atlas cluster is fully
compatible with the strongest possible two-primary phase.  The next exact
algebraic calculation should therefore determine whether \([q]\) is zero in
\(R/[P,R]\), before further large-dimensional optimization is devoted to
preserving it.
