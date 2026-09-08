# Characters of the full binary Leavitt unit group

2026-09-08. Written mathematical proof; no new Lean verification is claimed.
This proves a character classification, not a verdict on hyperlinearity.

Let

\[
R=L_{\mathbb F_2}(1,2),\qquad H=R^\times.
\]

Write the Leavitt generators as \(s_0,s_1,t_0,t_1\), so that
\(t_i s_j=\delta_{ij}\) and \(s_0t_0+s_1t_1=1\). For a finite binary
word \(\alpha\), write \(s_\alpha\) for its real prefix, \(t_\alpha\)
for the corresponding ghost prefix, and \(e_\alpha=s_\alpha t_\alpha\).
Let

\[
B_m=\operatorname{span}_{\mathbb F_2}
 \{s_\alpha t_\beta:|\alpha|=|\beta|=m\}
 \cong M_{2^m}(\mathbb F_2),\qquad K=\bigcup_m B_m^\times.
\]

A character here means any normalized, conjugation-invariant,
positive-definite function, with no extremality assumption.

**Theorem.** Every character of \(H\) has the form

\[
\boxed{\quad \varphi=a\,1+(1-a)\,\delta_1,\qquad 0\leq a\leq1.\quad}
\tag{1}
\]

The proof uses the already established inputs that \(H\) is infinite
simple, that its depth-two prefix identification with \(GL_4(R)\)
identifies this group with \(EL_4(R)\), and that

\[
\varphi|_K=a\,1+(1-a)\,\delta_1.
\tag{2}
\]

The first two inputs are recorded in
[the simplicity proof](../binary-leavitt-elementary-group-is-simple-proof.md)
and [the unit-group identification](../leavitt-gl-equals-el-and-perfect-unit-group.md).
For (2), apply [the finite-core character proof](../degree-zero-core-dirac-haar-proof.md)
with outer rank four: the tower \(SL_{4\cdot2^m}(\mathbb F_2)\) becomes
the same \(K\), after omitting finitely many initial stages. Its
dense-support character-ratio estimate is the only finite-group character
input. No classification theorem for arbitrary coefficient rings is assumed.

## 1. Single-sandwich division, directly from prefixes

Every nonzero \(a\in R\) admits \(b,c\in R\) with

\[
bac=1.
\tag{3}
\]

Here is an elementary proof that also permits \(b,c\) to be ghost and
real monomials. Expand \(a\) as a finite sum of spanning monomials.
By repeatedly inserting \(1=s_0t_0+s_1t_1\), make all right ghost
lengths equal to one \(N\), and collect terms:

\[
a=\sum_{|\beta|=N} P_\beta(s_0,s_1)t_\beta.
\tag{4}
\]

At least one formal polynomial \(P_\beta\) is nonzero; otherwise (4)
would say \(a=0\). Cancel repeated formal words in this polynomial and
write it as \(\sum_{i=1}^r s_{\alpha_i}\), with the \(\alpha_i\)
distinct. Choose an infinite binary sequence \(x\) that is not
eventually periodic. The infinite words \(\alpha_i x\) are distinct:
an equality for two comparable, distinct prefixes would make \(x\)
periodic. Choose a sufficiently long finite prefix \(\gamma\) of
\(x\) that the finite words \(\alpha_i\gamma\) are pairwise
prefix-incomparable. Prefix cancellation gives

\[
t_{\alpha_1\gamma}\,a\,s_{\beta\gamma}
=t_{\alpha_1\gamma}\sum_i s_{\alpha_i\gamma}=1.
\]

This proves (3). In particular, the argument does not presume linear
independence of the pure real words: it proves the required nonvanishing
by the final sandwich. The repository also has the internal theorem
`BinaryLeavitt.exists_mul_mul_eq_one` in
[LeavittSimplicity.lean](../../GroupApproximation/Leavitt/LeavittSimplicity.lean).

## 2. A character regular on the core vanishes on proper diagonal corners

A *diagonal projection* below is the sum of finitely many disjoint
cylinder idempotents. For such a projection \(p\), put

\[
H_p=\{1-p+u:u\in(pRp)^\times\}\leq H.
\]

Suppose \(0<p<1\) and \(\chi|_K=\delta_1\). We prove

\[
\chi(h)=0\qquad(h\in H_p\setminus\{1\}).
\tag{5}
\]

Refine the cylinder partition to a common depth with at least two
leaves outside \(p\). The resulting matrix identification writes

\[
h=G=\operatorname{diag}(A,I_l),\qquad A\in GL_m(R),
\quad A\neq I_m,\quad l\geq2.
\]

Choose a nonzero entry \(a=(A-I)_{ij}\), and choose \(b,c\) as in
(3). Let \(z\) be one of the spare coordinates. Given a ghost
prefix \(d=t_\alpha\), set

\[
k_d=I+E_{z i}\,db,\qquad G_d=k_d G k_d^{-1}.
\]

Each \(k_d\) is an involution. For distinct words \(\alpha,\beta\)
of the same length, put \(d=t_\alpha\), \(d'=t_\beta\).
Direct block multiplication gives

\[
G_d^{-1}G_{d'}=I+e_z v,\qquad
v=(d+d')b\,\operatorname{row}_i(A-I),
\tag{6}
\]

where \(v\) is supported on the first \(m\) coordinates. Its
\(j\)-th coefficient has a right inverse:

\[
\big((d+d')ba\big)c s_\alpha=(t_\alpha+t_\beta)s_\alpha=1.
\tag{7}
\]

Thus \(v:R^m\to R\) is a split surjection. We next check explicitly
that the unipotent in (6) is conjugate to a constant elementary root;
this step requires no freeness theorem for arbitrary projective modules.

Choose a right inverse column \(r\) with \(vr=1\), and let
\(N=e_zv\). Decompose the total right module into

\[
C=rR,\qquad I=e_zR,\qquad
D=\ker(v)\oplus R^{l-1}.
\]

The map \(N\) identifies \(C\cong R\) with \(I\cong R\) and
vanishes on \(D\oplus I\). Since
\(\ker(v)\oplus R\cong R^m\), the second spare coordinate gives

\[
D\cong R^{m+l-2}.
\]

These are exactly the three summands of a standard elementary
square-zero matrix in \(M_{m+l}(R)\). Choose module isomorphisms on
\(C,D,I\), choosing the map on \(I\) to intertwine \(N|_C\) with
the standard elementary map. Their direct sum conjugates \(I+N\)
to a constant elementary root. Under the equal-depth prefix matrix
identification this root belongs to \(B_q^\times\subset K\) for
the chosen depth \(q\). It is nonidentity by (7), so (6) has
character zero.

For any prescribed positive integer \(r_0\), take \(r_0\) distinct
ghost prefixes at one common length. In a tracial GNS realization
\((\pi,M,\tau)\) of \(\chi\), the vectors \(\pi(G_d)\) in
\(L^2(M,\tau)\) are then orthonormal, by (6), while
\(\tau(\pi(G_d))=\chi(G)\) for every \(d\). Hence

\[
|\chi(G)|
=\left|\tau\left(\frac1{r_0}\sum_d\pi(G_d)\right)\right|
\leq r_0^{-1/2}.
\]

Letting \(r_0\) grow proves (5). For a general core parameter
\(a\), the identical calculation instead gives
\(|\varphi(G)|^2\leq a\), but only (5) is needed below.

## 3. Conjugating a sufficiently small cylinder stays in a proper corner

Fix \(g\in H\). Write \(g\) and \(g^{-1}\) as finite sums of
prefix monomials. Let \(D\) bound every real and ghost length in
both sums, and let \(M_0\) be the total number of their terms.
Take a word \(\alpha\) of length \(n>D\), and set
\(e=e_\alpha\).

For a term \(s_u t_v\) of \(g\), its product with \(e\) is zero
unless \(\alpha=v\gamma\), in which case

\[
s_u t_v e=s_{u\gamma}t_\alpha.
\tag{8}
\]

Its left support is the cylinder \(u\gamma\), of length at least
\(n-D\). Similarly, for a term \(s_a t_b\) of \(g^{-1}\),
its product on the left by \(e\) is zero unless
\(\alpha=a\eta\), in which case

\[
e s_a t_b=s_\alpha t_{b\eta}.
\tag{9}
\]

Its right support is a cylinder of length at least \(n-D\).
Let \(p\) be the diagonal projection onto the union of the cylinder
\(\alpha\), all the left supports in (8), and all the right
supports in (9). Use the ordinary Bernoulli measure on binary cylinders
only to count this finite union. It has measure at most

\[
(M_0+1)2^{D-n}.
\]

For all sufficiently large \(n\), this is less than one, so \(p\)
is a proper diagonal projection. We have

\[
e\leq p,\qquad ge=pge,\qquad eg^{-1}=eg^{-1}p.
\tag{10}
\]

For \(k\in H_e\), write \(k-1=e(k-1)e\). Equations (10) show
that \(gkg^{-1}-1\in pRp\), with the same assertion for its
inverse. Consequently

\[
H_e\leq H_p,\qquad gH_e g^{-1}\leq H_p.
\tag{11}
\]

The projection \(p\) is fixed once \(g\) and \(e\) are chosen;
it works for every \(k\in H_e\). No invariant probability measure
for the action of \(H\) is asserted or used.

## 4. A nonidentity unit fails to centralize some cylinder group

For every \(g\neq1\) and every depth \(n\), some length-\(n\)
cylinder \(e\) has \([g,H_e]\neq1\).

Suppose otherwise at a fixed depth. In each \(eRe\cong R\), choose
the constant order-three matrix

\[
q_e=\begin{pmatrix}0&1\\1&1\end{pmatrix}
\]

using the two child cylinders of \(e\). Both \(q_e\) and
\(q_e-e\) are units of \(eRe\). The unit \(1-e+q_e\) belongs
to \(H_e\). Commutation of \(g\) with this unit, evaluated in
the two off-diagonal Peirce blocks, gives

\[
(1-e)ge(q_e-e)=0,\qquad
(q_e-e)eg(1-e)=0.
\]

Thus \(g\) commutes with \(e\). The element \(ege\) is a unit
of \(eRe\) and centralizes all its units. But
\((eRe)^\times\cong H\), whose center is trivial by infinite
simplicity. Hence \(ege=e\). Summing over the depth-\(n\)
partition yields \(g=1\), a contradiction.

## 5. Regularity on the core forces regularity on the whole group

Suppose \(\chi|_K=\delta_1\), and fix \(g\neq1\). Choose a
depth large enough for Section 3. By Section 4 there is a cylinder
\(e\) at that depth such that \(H_e\) does not centralize \(g\).
Its conjugation orbit of \(g\) is infinite. Indeed, a finite orbit
would give a homomorphism from the infinite simple group
\(H_e\cong H\) to a finite symmetric group; that homomorphism is
trivial, so the orbit would be a singleton.

Choose arbitrarily many distinct conjugates
\(g_i=k_i g k_i^{-1}\), with \(k_i\in H_e\). By (11),

\[
g_i g_j^{-1}
=k_i\,[g(k_i^{-1}k_j)g^{-1}]\,k_j^{-1}\in H_p.
\tag{12}
\]

When \(i\neq j\), this element is nonidentity. Its character is
zero by Section 2. Character invariance gives the same value for
\(g_j^{-1}g_i\), so the GNS vectors \(\pi(g_i)\) are pairwise
orthonormal. Each has trace \(\chi(g)\). The averaging argument
from Section 2 now proves \(\chi(g)=0\). Therefore

\[
\chi|_K=\delta_1\quad\Longrightarrow\quad\chi=\delta_1
\text{ on }H.
\tag{13}
\]

## 6. The core's trivial weight is the whole group's trivial weight

Take an arbitrary character \(\varphi\), realized in its finite
tracial GNS algebra \((M,\tau)\), and use the parameter \(a\) in
(2). Let \(P_K\in M\) be the projection onto the \(K\)-fixed
vectors, obtained as the strong limit of averages over its increasing
finite subgroups. Formula (2) gives

\[
\tau(P_K)=a.
\tag{14}
\]

Use the depth-two identification \(H=EL_4(R)\), under which
\(K=EL_4(R_0)\), where \(R_0=\bigcup_m B_m\). For any elementary
generator \(h=x_{ij}(r)\), choose \(k\neq i,j\) and let

\[
U=x_{ik}(R_0,+)\leq K.
\]

This is an infinite locally finite subgroup commuting with \(h\).
The same averaging calculation gives \(\tau(P_U)=a\). Since
\(U\leq K\), we have \(P_K\leq P_U\); faithfulness of the
GNS trace and equality of their traces imply \(P_K=P_U\). Thus
\(P_K\) commutes with \(\pi(h)\). Elementary generators generate
\(H\), so \(P_K\) is central in \(M\).

The representation of \(H\) on \(P_K\) is trivial on \(K\).
Its kernel is normal in \(H\) and contains the nontrivial subgroup
\(K\); simplicity makes it all of \(H\). Consequently

\[
\pi(g)P_K=P_K\qquad(g\in H).
\tag{15}
\]

If \(a=1\), (15) proves \(\varphi=1\). If \(a<1\), the
normalized trace on the complementary central corner defines a
character

\[
\chi(g)=\frac{\tau((1-P_K)\pi(g))}{1-a}
=\frac{\varphi(g)-a}{1-a}.
\]

Its restriction to \(K\) is \(\delta_1\). Equation (13) proves
\(\chi=\delta_1\), which gives (1).

## 7. Exact consequence for the hyperlinearity goal

The full-group character-classification obligation in
[the character-transfer audit](leavitt-character-transfer-audit-2026-09-05.md)
is now discharged by the written proof above. The other obligation
remains: construct an actual non-Connes-embeddable character of this
same \(H\), or directly exclude matrix microstates of \(\delta_1\).

More precisely, (1) implies that if \(H\) is hyperlinear, every
character of \(H\) is Connes embeddable: take direct sums of canonical
matrix microstates with scalar identity blocks. Conversely, a single
nonembeddable character of \(H\) would prove that \(H\) is not
hyperlinear. This classification does not construct such a character,
does not assert tracial extension from arbitrary subgroups, and supplies
neither a uniform Hilbert--Schmidt packet gap nor a full-kernel
microstate construction.

## 8. Which subgroup characters extend tracially

For every subgroup \(\Lambda\leq H\), a character \(\psi\)
of \(\Lambda\) extends to a character of \(H\) if and only if

\[
\psi=a\,1+(1-a)\,\delta_1\quad\text{on }\Lambda
\quad\text{for some }a\in[0,1].
\tag{16}
\]

Necessity is restriction of (1); sufficiency is the corresponding
ambient mixture. In particular, if \(\Lambda\) is known to be
hyperlinear, every extendible character of \(\Lambda\) is Connes
embeddable. No such assertion about the canonical trace is made for
an arbitrary subgroup without that hypothesis.

A nonembeddable character of a free subgroup, obtained by mapping its
generators into a nonembeddable finite factor, therefore cannot extend
tracially to \(H\). This is an obstruction to that proposed source
of a coefficient receiver, independent of how the free subgroup is
embedded.

## 9. What a finite tracial representation supplies as a coefficient receiver

Let \(\pi:H\to U(M)\) be a representation into a finite von Neumann
algebra with faithful normalized trace, and set \(N=\pi(H)''\).
The preceding proof gives a projection \(P\in Z(N)\), of trace
\(a\), on which \(H\) acts trivially. The projection need not be
central in the ambient \(M\). If \(a<1\), the normalized trace of
\(g\mapsto(1-P)\pi(g)\) is exactly \(\delta_1\). The
trace-preserving map on the complex group algebra therefore extends
to a normal isomorphism

\[
L(H)\ \cong\ (1-P)N,
\qquad \lambda_g\longmapsto(1-P)\pi(g).
\tag{17}
\]

This follows directly by the induced isometry of tracial GNS spaces.
Thus a nontrivial finite tracial representation supplies a copy of
the canonical factor, whose matrix approximability is the remaining
question.

The natural root invariant projections do not produce a nonzero
coefficient corner on that canonical component. For a finite
\(r\)-dimensional \(\mathbb F_2\)-subspace \(V\leq R\), fix
an elementary root and form its fixed projection

\[
p_V=2^{-r}\sum_{v\in V}\pi(x_{ij}(v)),\qquad
\tau(p_V)=a+(1-a)2^{-r}.
\tag{18}
\]

For any infinite additive subgroup \(W\leq R\), the decreasing
strong limit over finite subspaces of \(W\) has trace \(a\).
It contains \(P\), hence equals \(P\) by faithfulness of the
trace. In particular it is zero on the canonical component. This
applies to root groups with coefficients in every nonzero Leavitt
corner, as well as to the whole root group.

The single-element sign projections behave differently from ring
supports. For distinct nonzero coefficients \(u,v\in R\), put
\(q_u=(1-\pi(x_{ij}(u)))/2\), and similarly define \(q_v\).
Additivity of the root and (1) give

\[
\tau(q_u)=\frac{1-a}{2},\qquad
\tau(q_uq_v)=\frac{1-a}{4},\qquad
q_{u+v}=q_u+q_v-2q_uq_v.
\tag{19}
\]

Even when \(u=e_0\) and \(v=e_1\) are orthogonal ring idempotents,
these two projections have nonzero overlap in (19) whenever \(a<1\). They are
therefore not the orthogonal support projections of a representation
of the Leavitt coefficients. Equations (17)--(19) also hold in the
actual finite tracial algebra \(L(H)\); the same is true of every
formal group identity among the commuting corner copies. A negative
hyperlinearity argument consequently needs an additional property of
matrix approximability. Neither these invariant projections nor the
formal self-similarity identities provide that additional property.
