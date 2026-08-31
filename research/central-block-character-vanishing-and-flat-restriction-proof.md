---
rg: 2
id: central-block-character-vanishing-and-flat-restriction-proof
kind: route
title: Compute the unique central-block character and its abelian restrictions
target: unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra
requires:
  - true-bcs-predicates-are-local-finite-group-corners
---

# Compute the unique central-block character and its abelian restrictions

## 1. The selected left ideal has one basis vector per central coset

Let \(K\) be finite, let \(Z\leq Z(K)\), and fix
\(\lambda\in\widehat Z\).  Set

\[
 p=p_\lambda=\frac1{|Z|}\sum_{z\in Z}\overline{\lambda(z)}z.
 \tag{1}
\]

For every \(z_0\in Z\),

\[
 z_0p=\lambda(z_0)p.
 \tag{2}
\]

Choose a transversal \(T\) for \(K/Z\).  The vectors

\[
 \{pt:t\in T\}
 \tag{3}
\]

are a basis of \(p\mathbf C[K]\).  Indeed, their supports in the ordinary
group basis are the disjoint cosets \(Zt\), and every \(pg\) is a scalar
multiple of the vector indexed by \(gZ\).  Therefore

\[
 \dim_\mathbf C p\mathbf C[K]=[K:Z].
 \tag{4}
\]

Assume now that \(p\mathbf C[K]\) is a simple algebra \(M_d(\mathbf C)\).
Its left regular module is the direct sum of \(d\) copies of its unique
simple column module.  If \(\rho\) denotes the corresponding irreducible
\(K\)-representation, then

\[
 p\mathbf C[K]\cong \rho^{\oplus d}
 \quad\text{as left \(K\)-modules},
 \qquad
 [K:Z]=d^2.
 \tag{5}
\]

This also proves the equivalence between simplicity of the selected block
and uniqueness of the irreducible type above \(\lambda\).

## 2. The unique selected character vanishes off the center

Let \(L_g\) be left multiplication by \(g\in K\) on
\(p\mathbf C[K]\).  In the basis (3), \(L_g\) is a monomial matrix on the
coset set \(K/Z\).  A diagonal entry can occur only if

\[
 gtZ=tZ,
 \tag{6}
\]

or equivalently \(t^{-1}gt\in Z\).  Because \(Z\) is central, (6) implies
\(g\in Z\).  Hence

\[
 {\rm Tr}(L_g)=0\qquad(g\notin Z).
 \tag{7}
\]

If \(g\in Z\), equation (2) shows that \(L_g\) is
\(\lambda(g)I\) on the \([K:Z]=d^2\)-dimensional space, so

\[
 {\rm Tr}(L_g)=d^2\lambda(g).
 \tag{8}
\]

On the other hand, (5) gives

\[
 {\rm Tr}(L_g)=d\chi_\rho(g).
 \tag{9}
\]

Combining (7)--(9) proves

\[
 \chi_\rho(g)=
 \begin{cases}
 d\lambda(g),&g\in Z,\\
 0,&g\notin Z.
 \end{cases}
 \tag{10}
\]

No classification of groups of central type is used.

## 3. Restriction to every abelian subgroup is flat

Let \(H\leq K\) be abelian and let \(\eta\in\widehat H\).  Character
orthogonality and (10) give its multiplicity in \(\rho|_H\):

\[
\begin{aligned}
 m_\eta
 &=\frac1{|H|}\sum_{h\in H}\chi_\rho(h)\overline{\eta(h)}\\
 &=\frac d{|H|}\sum_{z\in H\cap Z}
       \lambda(z)\overline{\eta(z)}\\
 &=
 \begin{cases}
 \dfrac{d|H\cap Z|}{|H|},&
       \eta|_{H\cap Z}=\lambda|_{H\cap Z},\\[6pt]
 0,&\text{otherwise}.
 \end{cases}
\end{aligned}
 \tag{11}
\]

Thus every compatible character occurs, all with the common multiplicity

\[
 \frac d{[H:H\cap Z]}.
 \tag{12}
\]

The existence of the restriction already shows that the compatible set is
nonempty; alternatively, every character of a subgroup of a finite abelian
group extends to the whole group.  Formula (12) also records the divisibility

\[
 [H:H\cap Z]\mid d.
 \tag{13}
\]

Suppose \(H=\langle s_1,\ldots,s_k\rangle\) with commuting involutions
\(s_i\).  Then \(H\) and its character group are vector spaces over
\(\mathbf F_2\).  The condition

\[
 \eta|_{H\cap Z}=\lambda|_{H\cap Z}
 \tag{14}
\]

defines an affine coset in \(\widehat H\).  Evaluation

\[
 \eta\longmapsto(\eta(s_1),\ldots,\eta(s_k))
 \tag{15}
\]

is an affine-linear map into \(\{\pm1\}^k\), and it is injective because the
\(s_i\) generate \(H\).  Therefore its image is an affine subset of the
Boolean cube.  Equations (11)--(12) say that this image is exactly the joint
spectrum in \(\rho\), with constant joint-eigenspace rank.

For commuting elements of arbitrary finite orders the same proof applies
with finite abelian character groups.  The compatible characters form a
torsor for the annihilator of \(H\cap Z\), and evaluation on the chosen
elements maps that torsor to a coset of a finite subgroup of a product of
root-of-unity groups.

This proves the group-native obstruction.

## 4. A simple Heisenberg block exists in every matrix size

Fix \(D\geq2\).  It is useful to realize the presentation in UCB8 as the
set

\[
 H_D=(\mathbf Z/D\mathbf Z)^3
 \tag{16}
\]

with multiplication

\[
 (a,b,c)(a',b',c')
 =(a+a',\,b+b',\,c+c'+ba').
 \tag{17}
\]

With

\[
 x=(1,0,0),\qquad y=(0,1,0),\qquad z=(0,0,1),
 \tag{18}
\]

one has \(yx=zxy\), and every element has a unique normal form
\(x^ay^bz^c\).  Hence \(|H_D|=D^3\).  Commuting with \(x\) forces \(b=0\),
and commuting with \(y\) forces \(a=0\), so

\[
 Z(H_D)=\langle z\rangle.
 \tag{19}
\]

Let \(\zeta=\exp(2\pi i/D)\) and act on
\(\ell^2(\mathbf Z/D\mathbf Z)\) by

\[
 X e_t=e_{t+1},\qquad
 Y e_t=\zeta^t e_t,\qquad
 Z_0 e_t=\zeta e_t.
 \tag{20}
\]

Then \(YX=Z_0XY\), so (20) is a representation with central character
\(\lambda(z)=\zeta\).  It is irreducible: the distinct eigenspaces of \(Y\)
are the coordinate lines, while \(X\) acts transitively on those lines, so
an operator commuting with both is scalar.

The \(\lambda\)-block has dimension

\[
 [H_D:\langle z\rangle]=D^2.
 \tag{21}
\]

The irreducible representation (20) already contributes a simple summand of
dimension \(D^2\).  It therefore exhausts the whole block:

\[
 p_\lambda\mathbf C[H_D]\cong M_D(\mathbf C).
 \tag{22}
\]

Because \(D\geq2\) and \(\lambda\) is nontrivial,

\[
 {\rm aug}(p_\lambda)
 =\frac1D\sum_{j=0}^{D-1}\overline{\zeta^j}=0.
 \tag{23}
\]

Thus this is an augmentation-zero central selector, not a subgroup-average
corner.

## 5. Arbitrary relations live inside the block as Hecke projections

Let \(R\subseteq A\times B\) be nonempty.  Choose
\(D\geq\max(2,|R|)\) and a surjection

\[
 \theta:\mathbf Z/D\mathbf Z\longrightarrow R.
 \tag{24}
\]

Inside the matrix block (22), set

\[
 P_a=\sum_{\theta(t)\in\{a\}\times B}|e_t\rangle\langle e_t|,
 \qquad
 Q_b=\sum_{\theta(t)\in A\times\{b\}}|e_t\rangle\langle e_t|.
 \tag{25}
\]

These are elements of \(p_\lambda\mathbf C[H_D]\), because (22) is the
entire matrix algebra.  The \(P_a\) are pairwise orthogonal and sum to the
corner unit; the same is true of the \(Q_b\); and the two families commute.
Moreover,

\[
 P_aQ_b
 =\sum_{\theta(t)=(a,b)}|e_t\rangle\langle e_t|,
 \tag{26}
\]

which is nonzero exactly for \((a,b)\in R\).  Hence the joint support is
precisely \(R\), while (22) guarantees that there is no other irreducible
sector with the chosen central character.

If \(R\) is nonaffine, Section 3 proves that the coordinate reflections
formed from (25), for example

\[
 S=\sum_a\epsilon_aP_a,\qquad
 T=\sum_b\delta_bQ_b,
 \tag{27}
\]

cannot all be images of commuting group elements whenever their joint
eigenvalue support retains the nonaffine relation.  They are legitimate
elements of the finite group algebra, but not a group-native selector tuple.

## 6. Why a normal Heisenberg subgroup does not evade the dichotomy

Let \(N\triangleleft L\) be finite, suppose \(Z\leq Z(N)\) is preserved by
\(L\), and suppose \(N\) has a unique irreducible type \(\sigma\) above the
chosen \(L\)-invariant central character.  Clifford theory then says that
every irreducible \(L\)-representation above that character restricts to

\[
 \pi|_N\cong \sigma^{\oplus m_\pi}.
 \tag{28}
\]

This is useful isotypy, but it controls only \(N\).  After choosing an
identification of the space with \(H_\sigma\otimes\mathbf C^{m_\pi}\), an
extension element acts as an implementer of its automorphism of \(N\)
tensored with an operator on the multiplicity space.  Different projective
representations on that second factor are precisely the hidden extension
sectors.

There are therefore two possibilities.  If predicate coordinates are kept
inside \(N\), Sections 2--3 force their commuting joint group spectrum to be
affine.  If extension elements are used, Stone--von Neumann uniqueness does
not control their multiplicity operators.  Imposing uniqueness for the
whole selected \(L\)-block removes those operators, but then Sections 1--3
apply to \(L\) itself and again force every commuting group-element spectrum
to be affine.

The only positive arbitrary-predicate realization left by this dichotomy is
the Hecke-operator construction (25).  To globalize it one must identify
linear combinations of finite-group elements across overlapping contexts.
Ordinary solution-group relators and subgroup amalgamation identify group
elements, not such sums.  Proving a positive canonical-trace groupification
of those Hecke equalities is exactly the residual gate.
