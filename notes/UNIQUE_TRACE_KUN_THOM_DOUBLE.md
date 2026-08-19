# The Kun--Thom symmetric double has unique reduced trace

This note isolates a reduced-\(C^*\) endpoint for the hyperlinear-versus-sofic
problem which is independent of the phase and one-trace constructions in
`notes/NOTEPAD.md`.

Throughout this note take the explicit Kun--Thom pair with \(q=2\) and
\(r,d\geq 3\):

\[
 R_+=\mathbb F_2[x_1,\ldots,x_d],\qquad
 R=\mathbb F_2[x_1^{\pm1},\ldots,x_d^{\pm1}],
\]

\[
 \Gamma=\operatorname{EL}_r(R_+),\qquad
 G=\operatorname{EL}_r(R)\rtimes\operatorname{SL}_d(\mathbb Z).
\]

Kun--Thom prove that \(G\) and \(\Gamma\) are residually finite Kazhdan
groups and that \(\Gamma<G\) is infranormal but not normal
([Theorem E](https://arxiv.org/html/2608.06222v1)).  Put

\[
 D=G*_{\Gamma}G.
\]

The weak/operator-norm MF and nonsofic properties of \(D\) are proved in
`WEAK_MF_NONSOFIC_DOUBLE.md`.  The result below concerns the reduced group
algebra, not the auxiliary MF completion used there.

## 1. The polynomial subgroup has trivial core

**Lemma 1.**  The normal core of \(\Gamma\) in \(G\) is trivial:

\[
 \operatorname{core}_G(\Gamma)
 =\bigcap_{g\in G}g\Gamma g^{-1}=\{1\}.
\]

**Proof.**  It is enough to prove that every normal subgroup \(N\lhd G\)
contained in \(\Gamma\) is trivial.  Take \(z=(z_{kl})\in N\).  Its entries
belong to \(R_+\).  For \(i\ne j\), \(a\in R\), and the matrix unit
\(E=E_{ij}\), normality gives

\[
 (1+aE)z(1-aE)
 =z+a(Ez-zE)-a^2EzE\in N\subseteq\operatorname{EL}_r(R_+).       \tag{1}
\]

Choose \(a=x_1^{-m}\), where \(m\) is arbitrarily large.  If \(k\ne j\),
the \((i,k)\)-entry of (1) is

\[
 z_{ik}+x_1^{-m}z_{jk}.
\]

It belongs to \(R_+\) for every \(m\).  A fixed nonzero polynomial
\(z_{jk}\) acquires a negative \(x_1\)-exponent when \(m\) is sufficiently
large, and that lowest exponent cannot be cancelled by the fixed polynomial
\(z_{ik}\).  Hence \(z_{jk}=0\) for every \(k\ne j\).  Varying \(j\) shows
that \(z\) is diagonal.

For diagonal \(z\), the \((i,j)\)-entry of (1) is

\[
 x_1^{-m}(z_{jj}-z_{ii}).
\]

Again this is polynomial for every \(m\), so all diagonal entries are equal.
Thus \(z=c1_r\).  Because \(z\in\operatorname{GL}_r(R_+)\), the scalar
\(c\) is a unit of \(R_+\).  The only unit of the polynomial ring over
\(\mathbb F_2\) is \(1\).  Therefore \(z=1\), and \(N=1\). \(\square\)

The use of \(q=2\) removes all scalar-center bookkeeping.  For general
\(q\), the same argument says that the core is contained in the constant
scalar center.

## 2. Faithfulness of the Bass--Serre action

Let \(T\) be the Bass--Serre tree of \(D=G*_{\Gamma}G\).

**Lemma 2.**  The action \(D\curvearrowright T\) is faithful, minimal, and
non-elementary.

**Proof.**  An element in the kernel fixes a vertex of the first type and
therefore belongs to its stabilizer \(G\).  It also fixes every edge adjacent
to that vertex.  The intersection of the adjacent edge stabilizers is
\(\operatorname{core}_G(\Gamma)\), which is trivial by Lemma 1.  Thus the
action is faithful.

The standard Bass--Serre action of a reduced one-edge amalgam is minimal.
Here both edge embeddings are proper.  In fact \([G:\Gamma]=\infty\), since
the projection \(G\to\operatorname{SL}_d(\mathbb Z)\) is trivial on
\(\Gamma\).  Consequently \(T\) is not a line, and the amalgam action is
non-elementary. \(\square\)

## 3. Trivial amenable radical

**Theorem 3.**  The amenable radical of \(D\) is trivial.

**Proof.**  Let \(A\lhd D\) be amenable.  An amenable group cannot act
non-elementarily on a tree: otherwise two independent hyperbolic elements
give a nonabelian free subgroup by ping-pong.  Hence the action of \(A\) is
elementary.

If \(A\) contains a hyperbolic element, its limit set in \(\partial T\) has
at most two points.  Normality makes that finite limit set \(D\)-invariant,
contradicting the non-elementarity of \(D\curvearrowright T\).  If every
element of \(A\) is elliptic but \(A\) has no global fixed vertex, the
standard elliptic-action lemma gives a unique fixed end; normality again
makes it \(D\)-invariant, the same contradiction.

Thus \(A\) has a nonempty fixed subtree.  That subtree is \(D\)-invariant by
normality.  Minimality forces it to be all of \(T\), so \(A\) lies in the
kernel of the action.  Lemma 2 makes that kernel trivial. \(\square\)

## 4. Unique trace and the reduced-MF endpoint

The Breuillard--Kalantar--Kennedy--Ozawa unique-trace theorem says that a
discrete group has trivial amenable radical exactly when its reduced group
\(C^*\)-algebra has a unique tracial state; see, for example,
[Haagerup's proof](https://arxiv.org/abs/1509.05880).

**Corollary 4.**  \(C_r^*(D)\) has a unique tracial state, namely its
canonical regular trace.

This turns a standard reduced-\(C^*\) approximation property into the exact
missing trace.

**Theorem 5 (reduced-MF counterexample criterion).**  If \(C_r^*(D)\) is an
MF \(C^*\)-algebra, then \(D\) is hyperlinear and nonsofic.  Consequently,
not every hyperlinear group is sofic.

**Proof.**  An MF embedding gives

\[
 \Phi:C_r^*(D)\longrightarrow
 \prod_n M_{k_n}(\mathbb C)\Big/\bigoplus_n M_{k_n}(\mathbb C).
\]

Choose a free ultrafilter and compose with the canonical map from the norm
matrix quotient to the normalized tracial matrix ultraproduct.  Pulling back
the ultraproduct trace gives a tracial state \(\tau_\Phi\) on \(C_r^*(D)\).
By Corollary 4 it is the canonical regular trace \(\tau_D\).

The regular trace is faithful on \(C_r^*(D)\).  Hence the composite into the
tracial ultraproduct has zero kernel: if its image of \(b\) is zero, then
\(\tau_D(b^*b)=0\), so \(b=0\).  It extends normally to a trace-preserving
embedding of \(L(D)\) into a matrix tracial ultraproduct.  Thus \(D\) is
hyperlinear.

The nonsoficity of \(D\) is the Kun--Thom centralizer-normalization argument
recorded in `WEAK_MF_NONSOFIC_DOUBLE.md`. \(\square\)

## 5. Exact remaining distinction

The already constructed MF algebra

\[
 B=C^*(\rho(G))*_{C^*(\rho(\Gamma))}C^*(\rho(G))
\]

surjects onto \(C_r^*(D)\), but MF is not preserved by arbitrary quotients.
Therefore Theorem 5 does not by itself finish the main problem.  It does,
however, remove all trace-selection ambiguity from the reduced target:

\[
 \boxed{C_r^*(G*_{\Gamma}G)\text{ is MF?}}
\]

is now a single sufficient certificate.  Any norm-matrix embedding of this
particular reduced algebra automatically carries the correct trace; no
square-root dimension profile or separate trace estimate is required.

There is also a formally stronger but sometimes convenient certificate.  If
the auxiliary full amalgam \(B\) is QWEP, then its quotient
\(C_r^*(D)\) is QWEP.  The GNS von Neumann algebra of the unique regular
trace is then QWEP, hence Connes embeddable by Kirchberg's finite-von-Neumann
QWEP criterion.  Thus

\[
 B\text{ is QWEP}\quad\Longrightarrow\quad D\text{ is hyperlinear and
 nonsofic}.                                                     \tag{2}
\]

Weak MF alone cannot discharge (2).  Although the norm matrix corona is
QWEP, QWEP is not inherited by arbitrary C*-subalgebras.  The standard sharp
warning is \(C^*(\mathbb F_\infty)\): it is residually finite-dimensional
(hence MF), while QWEP for this algebra is Kirchberg's QWEP conjecture and is
false after the negative solution of Connes embedding.  Therefore a proof of
(2) must use the special amalgam, not only its MF embedding.

## 6. The natural MF trace is provably outside the reduced dual

The failure of the existing weak-MF construction to reach the reduced
algebra is not just an absence of trace bookkeeping.  Its most natural trace
belongs to the wrong weak-containment class.

Let

\[
 r:D=G*_{\Gamma}G\longrightarrow G
\]

be the fold retraction and put \(K=\ker r\).

**Lemma 6.**  The group \(K\) is free of rank \(|G/\Gamma|-1\).  In
particular it is a nonabelian free group of infinite rank.

**Proof.**  The fold map is injective on every conjugate of either vertex
group.  Consequently \(K\) has trivial intersection with all vertex
stabilizers in the Bass--Serre tree and therefore acts freely on the tree.
Thus \(K\) is a free group.

The quotient graph \(K\backslash T\) has two vertices, because
\(D/K=G\) acts transitively on the vertices of each of the two types.  Its
edges are indexed by

\[
 (D/K)/(\Gamma K/K)=G/\Gamma.
\]

It is therefore the graph with two vertices and \(|G/\Gamma|\) parallel
edges.  Its fundamental group, which is \(K\), has rank
\(|G/\Gamma|-1\).  The index is infinite by Lemma 2. \(\square\)

The regular trace of \(G\) pulls back through \(r\) to the fold character

\[
 \chi_{\rm fold}(w)=\delta_e(r(w))=1_K(w).              \tag{3}
\]

It is Connes embeddable because \(G\) is residually finite, but it kills
every fold-difference, including the element \(a\) in the companion
one-trace criterion.

**Proposition 7.**  The GNS representation of \(\chi_{\rm fold}\) is not
weakly contained in the left regular representation of \(D\).  Equivalently,
\(\chi_{\rm fold}\) does not extend to a tracial state on \(C_r^*(D)\).

**Proof.**  Its GNS representation is the quasi-regular representation
\(\lambda_{D/K}=\lambda_G\circ r\).  If it were weakly contained in
\(\lambda_D\), restriction to the normal subgroup \(K\) would give

\[
 1_K\prec \lambda_D|_K.
\]

The restricted regular representation is a multiple of \(\lambda_K\).
Hence \(1_K\prec\lambda_K\), which is equivalent to amenability of \(K\).
This contradicts Lemma 6. \(\square\)

Thus unique trace does exactly what it should once an approximation factors
through \(C_r^*(D)\), but the trace furnished by the fold/profinite sector
cannot factor through that quotient.  A successful construction must change
the weak-containment class, not merely renormalize the existing fold trace.
