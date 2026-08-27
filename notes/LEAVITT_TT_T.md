# Global quasi-cocycle rigidity for the binary Leavitt elementary group

Let

\[
L=L_{\mathbf F_2}(1,2),\qquad G=E_5(L)=GL_5(L),
\]

and let

\[
H=\operatorname{diag}(E_4(L),1)=\operatorname{diag}(GL_4(L),1).
\]

This note proves that (G) has property ((TT)/T).  The same proof gives
Mimura's ((FF_{L_p})/T), (1<p<\infty).  The point not supplied by the
general noncommutative-universal-lattice theorem is bounded generation; it
follows here from the strong two-sided division property of (L).

## Inputs

The following algebraic inputs are proved in the repository.

1. Every nonzero (x\in L) admits (p,q\in L) such that (pxq=1)
   (`Leavitt/LeavittSimplicity.lean`).
2. (GL_m(L)=E_m(L)) for every (m\geq2)
   (`KOne/AllRanksElementary.lean`).

For the rigidity input, write (A=\mathbf Z\langle X_1,\ldots,X_k\rangle)
for a finite free noncommutative ring mapping onto (L).  Mimura,
Proposition 9.2.8, proves that

\[
E_5(A)\geq E_4(A)
\]

has relative ((TT)/T), and relative ((FF_{L_p})/T) for every
(1<p<\infty).  These relative properties pass to quotient pairs, so they
hold for (G\geq H).

## Uniform elimination

### Lemma

Let (R\neq0) be a ring satisfying

\[
x\neq0\Longrightarrow \exists p,q\in R\quad pxq=1.
\]

For every (n\geq2) and (A\in GL_n(R)), there are products (E,F) of
elementary transvections and (u\in R^\times) such that

\[
EAF=\operatorname{diag}(u,1,\ldots,1),
\]

where the total number of transvections occurring in (E) and (F) is at
most

\[
n^2+4n-5.
\]

### Proof

Induct on (n).  The first row of an invertible matrix is nonzero.  Using
at most three elementary transvections for a signed column swap, arrange
that (a=A_{11}\neq0).  Put (b=A_{12}), and choose (p,q\in R) with
(paq=1).  Set

\[
\rho=q(1-pb).
\]

Right multiplication by (t_{12}(\rho)) changes the ((1,2))-entry to

\[
b'=a\rho+b,
\qquad pb'=pa q(1-pb)+pb=1.
\]

Let (d') denote the resulting ((2,2))-entry.  Left multiplication by

\[
t_{21}((1-d')p)
\]

makes the ((2,2))-entry equal to

\[
(1-d')pb'+d'=1.
\]

Now left multiply by (t_{12}(-b')), and right multiply by
(t_{21}(-c')), where (c') is the then-current ((2,1))-entry.  This
clears positions ((1,2)) and ((2,1)).

For each (j\geq3), right multiply by
(t_{2j}(-A_{2j})).  Since (A_{22}=1), these operations make row (2)
the second standard row.  Then, for each (i\geq3), left multiply by
(t_{i2}(-A_{i2})).  These operations clear column (2) without changing
the complementary block.  The resulting matrix is (B\oplus1), with
(B\in GL_{n-1}(R)) on coordinates (1,3,\ldots,n).  Apply the inductive
hypothesis to (B).

At block size (m), the construction uses at most

\[
3+4+2(m-2)=2m+3
\]

transvections.  Hence the total is at most

\[
\sum_{m=2}^n(2m+3)=n^2+4n-5.
\]

This proves the lemma.  (square)

## Bounded generation, uniformly in the rank

Applying the full lemma to (R=L) and (n=5) uses at most (40)
transvections.  The remaining diagonal belongs to (H), because

\[
\operatorname{diag}(u,1,1,1)\in GL_4(L)=E_4(L).
\]

Let

\[
N_+=\langle t_{i5}(a):1\leq i\leq4, a\in L\rangle,
\qquad
N_-=\langle t_{5j}(a):1\leq j\leq4, a\in L\rangle.
\]

Every elementary transvection avoiding coordinate (5) lies in (H),
and every remaining transvection lies in (N_+\cup N_-).  Moving the left
elementary factors across the equality only replaces transvections by
their inverses.  Therefore

\[
G=(H\cup N_+\cup N_-)^{41}. \tag{1}
\]

This is exactly the bounded-generation hypothesis absent from the general
noncommutative case in Mimura's Proposition 9.2.8.

For the subgroup-only form, the full induction is unnecessary.  Perform
only the first elimination stage and stop as soon as one coordinate has
been isolated.  The residual complementary block is already an element of
a coordinate conjugate of (H).  Moreover, instead of a three-transvection
signed swap, if the ((1,1))-entry is zero one may add any column containing
a nonzero entry of the first row to the first column.  This costs one
transvection and makes the corner nonzero.  Thus the first rank-five stage
uses at most

\[
1+4+2(5-2)=11
\]

transvections, followed by one rank-four block.

Every root transvection lies in a conjugate of (H): choose a coordinate
outside the two indices used by the root and take the rank-four coordinate
block omitting it.  Only five such blocks occur, and they are fixed
conjugates of (H) by coordinate permutations in (GL_5(L)=E_5(L)).
Consequently there are fixed conjugates (H_1,\ldots,H_5) of (H) such that

\[
G=(H_1\cup\cdots\cup H_5)^{12}. \tag{2}
\]

The subgroup-only argument is rank-independent.  For (n\geq3), put

\[
G_n=GL_n(L)=E_n(L),\qquad
H_n=\operatorname{diag}(GL_{n-1}(L),1).
\]

The first elimination stage uses at most

\[
1+4+2(n-2)=2n+1
\]

transvections and leaves one element of a coordinate copy of (H_n).  Every
root transvection belongs to a coordinate copy of (H_n), since one can omit
an index different from its row and column.  Thus, for the (n) fixed
coordinate copies (H_{n,1},\ldots,H_{n,n}),

\[
G_n=(H_{n,1}\cup\cdots\cup H_{n,n})^{2n+2}. \tag{3}
\]

No rank-stability theorem is hidden here: equation (3) is obtained by one
explicit pivot and the identities (GL_m(L)=E_m(L)) already proved for every
(m\geq2).

## Consequences

### Theorem

For every (n\geq3), the group

\[
E_n(L_{\mathbf F_2}(1,2))
\]

has property ((TT)/T).  For every (n\geq4) and (1<p<\infty), it also has
Mimura's property ((FF_{L_p})/T).

### Proof

Fix (n\geq3).  The quotient of Mimura's relative theorem gives relative
((TT)/T) for (G_n\geq H_n).  Equivalently, a quasi-cocycle into a unitary
representation without invariant vectors is bounded on (H_n).  It is then
bounded on each fixed conjugate (H_{n,i}): expand
(b(g_i h g_i^{-1})) and use the fixed values (b(g_i)), (b(g_i^{-1})) and
the quasi-cocycle defect.  Equation (3), followed by the quasi-cocycle
triangle inequality at most (2n+1) times, bounds it on (G_n).

For (n\geq4), Mimura's relative ((FF_{L_p})/T) theorem and the same root
bounded-generation argument give the Banach conclusion.  (square)

Finally, property ((TT)/T) is invariant under central quotients and under
central extensions whose total group has property ((T)).  Hence the
universal Steinberg cover

\[
St_5(L)\longrightarrow E_5(L)
\]

also has property ((TT)/T).

More generally, for every (n\geq5), (St_n(L)\to E_n(L)) is the universal
central extension and (St_n(L)) has property ((T)).  Therefore (St_n(L))
and every quotient (St_n(L)/C), (C\leq Z(St_n(L))), have property
((TT)/T).  These quotients include the entire canonical family of
nonsofic central covers established elsewhere in the project.

## Relation-module form of the missing cohomology

The two-chart atlas gives a precise description of the ordinary second
cohomology which remains uncontrolled.  Write

\[
 P=A*B,\qquad A\cong B\cong A_8,
\]

and let

\[
 1\longrightarrow N\longrightarrow P\longrightarrow U\longrightarrow1
\]

be the presentation of the universal Steinberg cover proved in
`notes/EXPLICIT_LEAVITT_ATLAS.md`.  Put

\[
 M=N/[N,N],
\]

with its conjugation action by \(U\).  For every unitary \(U\)-module \(V\), the
Lyndon--Hochschild--Serre five-term sequence and Bass--Serre
Mayer--Vietoris sequence give a natural short exact sequence

\[
 0\longrightarrow V/(V^A+V^B)
 \longrightarrow \operatorname{Hom}_{\mathbb Z[U]}(M,V)
 \longrightarrow H^2(U,V)\longrightarrow0.             \tag{4}
\]

Indeed, property \((T)\) gives \(H^1(U,V)=0\).  Averaging over the two finite
factors gives \(H^j(A,V)=H^j(B,V)=0\) for \(j>0\), whence

\[
 H^2(P,V)=0,
 \qquad H^1(P,V)\cong V/(V^A+V^B).
\]

Since \(N\) acts trivially on \(V\), the middle term in the five-term sequence
is

\[
 H^1(N,V)^U=\operatorname{Hom}_{\mathbb Z[U]}(M,V),
\]

which proves (4).  The first arrow is explicit: a vector \(v\) defines the
\(P\)-cocycle which vanishes on \(A\) and restricts to
\(b\mapsto\pi(b)v-v\) on \(B\), and one then restricts this cocycle to \(N\).

The kernel \(N\) is finitely normally generated, so \(M\) is finitely
generated as a \(\mathbb Z[U]\)-module.  Consequently the missing
\(2\)-Kazhdan assertion is exactly the surjectivity, for every unitary
module, of the first arrow in (4).  This finite-generator
relation-module problem is the algebraic interface between the atlas and
the cohomological correction route.

This module also has a relator-free Bass--Serre model.  The kernel \(N\)
acts freely on the Bass--Serre tree of \(A*B\), because its quotient map is
injective on both factors.  The quotient graph has one edge orbit and two
vertex orbits, giving an exact sequence of \(\mathbb Z[U]\)-modules

\[
 0\longrightarrow M\longrightarrow\mathbb Z[U]
 \longrightarrow\mathbb Z[U/A]\oplus\mathbb Z[U/B]
 \longrightarrow\mathbb Z\longrightarrow0.             \tag{5}
\]

If

\[
 e_A=|A|^{-1}\sum_{a\in A}a,
 \qquad e_B=|B|^{-1}\sum_{b\in B}b,
\]

then, after complexification,

\[
 M_{\mathbb C}
 \cong\{x\in\mathbb C[U]:xe_A=xe_B=0\}.                \tag{6}
\]

In a unitary representation the two averaging elements act as the
orthogonal projections onto \(V^A\) and \(V^B\).  Thus (4)--(6) reduce the
remaining cohomology to an extension problem from one simultaneous
averaging kernel.  A spectral projection in a group \(C^*\)-completion is
not by itself enough: the maps in (4) are algebraic equivariant maps and
need not extend continuously.  What would suffice is an algebraic splitting
at \(M\), or a uniform bounded-extension theorem for all maps in (4).

Property \((T)\) does remove one possible analytic pathology in (4).  The
finite generating set \(A\cup B\) is a Kazhdan set; let \(\kappa>0\) be a
Kazhdan constant.  If unit vectors

\[
 \xi\in V^A\ominus V^U,
 \qquad \eta\in V^B\ominus V^U
\]

are phased so that \(\langle\xi,\eta\rangle\geq0\), then

\[
 \kappa\leq
 \max_{s\in A\cup B}\|\pi(s)\xi-\xi\|
 \leq2\|\xi-\eta\|.
\]

It follows that

\[
 |\langle\xi,\eta\rangle|\leq1-\kappa^2/8.             \tag{7}
\]

Thus \(V^A+V^B\) is closed, with a uniform angle bound over all unitary
representations.  The left term of (4) is therefore a uniformly
well-conditioned Hilbert quotient.  The unresolved issue is genuinely
extension from the simultaneous kernel (6), not closure of the sum of the
two fixed subspaces.

There is a sharper boundary on what an analytic extension argument could
detect. Give \(M_{\mathbb C}\) the norm inherited from its inclusion in
\(\ell^2(U)\), and write

\[
 W=\overline{M_{\mathbb C}}^{\ell^2(U)}.
\]

**Proposition (continuous relation maps are cohomologically trivial).** If
\(V\) is a unitary \(U\)-module and

\[
 T:M_{\mathbb C}\longrightarrow V
\]

is \(U\)-equivariant and bounded for the inherited \(\ell^2\)-norm, then
\(T\) lies in the image of the first arrow in (4). Consequently every
nonzero class in \(H^2(U,V)\) is represented by an algebraic equivariant map
on \(M_{\mathbb C}\) which is discontinuous in the regular \(\ell^2\)-norm.

**Proof.** The map \(T\) extends continuously to a \(U\)-intertwiner
\(\overline T:W\to V\). Since \(W\) is invariant under the left regular
representation, the orthogonal projection \(P_W:\ell^2(U)\to W\) commutes
with \(U\). Thus

\[
 S=\overline T P_W:\ell^2(U)\longrightarrow V
\]

is a bounded \(U\)-intertwiner extending \(T\). Put
\(v=-S\delta_1\). For \(x=\sum_g c_g g\in M_{\mathbb C}\), equivariance gives

\[
 T(x)=S(x)=\sum_g c_g\pi(g)S\delta_1=-\pi(x)v.       \tag{8}
\]

Under the Bass--Serre identification (5), the first arrow in (4) sends
\(v\) to precisely the map \(x\mapsto-\pi(x)v\). To check the sign directly,
make the cocycle zero on \(A\) and equal to
\(b\mapsto\pi(b)v-v\) on \(B\). On the oriented edge from \(gA\) to \(gB\),
the resulting equivariant edge cochain is \(-\pi(g)v\); evaluation on the
cycle \(x=\sum_g c_g g\) is the right side of (8). Therefore \(T\) is in
the image. Exactness of (4) proves the final assertion. \(\square\)

This proposition explains why the spectral projection associated with the
uniform angle in (7) cannot by itself produce or obstruct the missing
cohomology. Spectral calculus, bounded intertwiners, and Hilbert-module
orthogonal projections see only the continuous part of the relation module,
and that entire part already dies in \(H^2\). A successful nonvanishing
argument would have to construct a genuinely discontinuous algebraic module
map; a vanishing argument must prove an automatic-continuity theorem from the
special finite presentation of \(M\).

## Exact remaining frontier

For the Steinberg cover (U=St_5(L)), superperfectness handles trivial
coefficients and the theorem above makes the comparison map

\[
H_b^2(U,\mathcal H_\pi)\longrightarrow H^2(U,\mathcal H_\pi)
\]

injective whenever (pi) has no invariant vectors.  What is not proved is

\[
H^2(U,\mathcal H_\pi)=0
\quad\text{for every unitary }\pi.
\]

That is the remaining (2)-Kazhdan/cohomological correction problem.  The
present theorem does not by itself prove Frobenius stability, normalized
Hilbert--Schmidt stability, nonhyperlinearity, or a hyperlinear nonsofic
counterexample.

## Source pin

Masato Mimura, *Rigidity theorems for universal and symplectic universal
lattices*, Proposition 9.2.8 and Theorem 8.1.7.  Proposition 9.2.8 states
relative ((TT)/T) for (E_m(A)\geq E_{m-1}(A)), (m\geq3), and relative
((FF_{L_p})/T), (m\geq4), for a finite free noncommutative ring (A).
Its proof explicitly identifies bounded generation as the missing condition
for the corresponding global conclusion.
