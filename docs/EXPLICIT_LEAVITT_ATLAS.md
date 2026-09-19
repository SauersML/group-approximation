# An explicit finite superperfect atlas for the binary Leavitt unit group

This note makes the finite source in the exact-atlas Hilbert--Schmidt
criterion concrete.  Put

\[
  L=L_{\mathbb F_2}(1,2),\qquad Q=L^\times.
\]

Write the two real edges as \(e,f\), and put

\[
  (\gamma_1,\gamma_2,\gamma_3)=(ee,ef,f),
  \qquad S=\{e,f,e^*,f^*\}.
\]

## 1. Thirty explicit generators

For \(i\ne j\) in \(\{1,2,3\}\) and
\(a\in S\cup\{1\}\), define

\[
  q_{ij,a}=1+\gamma_i a\gamma_j^*\in Q.                 \tag{1}
\]

There are \(6\cdot5=30\) such elements.

**Proposition.**  The elements in (1) generate \(Q\).

**Proof.**  The set \(S\) generates \(L\) as a unital ring.  Khanh--Thanh,
Theorem 5.3, applied to the ordered leaf set
\(C=(ee,ef,f)\), says that

\[
  \Theta_C(x_{ij}(a))=1+\gamma_i a\gamma_j^*
  \quad(i\ne j,\ a\in S\cup\{1\})
\]

generates
\(\Theta_C(E_3(L))=L^\times\).  These are precisely the elements (1).
\(\square\)

Every \(q_{ij,a}\) is a scalar leaf transvection.  More explicitly, set

\[
(\alpha_{ij,a},\beta_{ij,a})=
\begin{cases}
  (\gamma_i,\gamma_j),&a=1,\\
  (\gamma_i a,\gamma_j),&a\in\{e,f\},\\
  (\gamma_i,\gamma_j b),&a=b^*,\ b\in\{e,f\}.
\end{cases}                                               \tag{2}
\]

Then

\[
  q_{ij,a}=1+\alpha_{ij,a}\beta_{ij,a}^*.
\]

The two paths in (2) are prefix-incomparable: \(\gamma_i\) and
\(\gamma_j\) are distinct leaves, and extending either path preserves
prefix-incomparability.  Lemma 2.2 of Khanh--Thanh extends the pair to a
finite leaf set \(D_{ij,a}\).  Relative to its matrix units,
\(q_{ij,a}\) is the elementary scalar matrix

\[
  I+E_{\alpha_{ij,a},\beta_{ij,a}}
  \in \operatorname{GL}_{|D_{ij,a}|}(\mathbb F_2).        \tag{3}
\]

In particular, \(q_{ij,a}\ne1\) and \(q_{ij,a}^2=1\).

## 2. Three finite Schur-cover charts

For \(k\in\{1,2,3\}\), let

\[
  D_k=(C\setminus\{\gamma_k\})
      \cup\{\gamma_ke,\gamma_kf\}.                        \tag{4}
\]

This is a four-leaf set and determines a scalar subgroup

\[
  K_k=\operatorname{GL}(D_k,\mathbb F_2)
     \cong\operatorname{GL}_4(\mathbb F_2)
     \cong A_8.                                           \tag{5}
\]

The thirty generators distribute among these three subgroups as follows:

* \(q_{ij,e}\) and \(q_{ij,f}\) belong to the \(D_i\)-chart;
* \(q_{ij,e^*}\) and \(q_{ij,f^*}\) belong to the \(D_j\)-chart;
* \(q_{ij,1}\) belongs to the \(D_k\)-chart for the unique
  \(k\notin\{i,j\}\).

Three scalar charts are necessary if every generator in (1) must itself
belong to one of the charts.  Indeed, if a finite
scalar leaf chart contains \(1+\alpha\beta^*\), then the two cylinder
projections \(\alpha\alpha^*\) and \(\beta\beta^*\) have the same matrix
rank in that chart.  For fixed \(i\ne j\), write \(m(\alpha)\) for the
number of chart leaves below the path \(\alpha\).  Containment of
\(q_{ij,1}\), \(q_{ij,e}\), and \(q_{ij,e^*}\), respectively, forces

\[
 m(\gamma_i)=m(\gamma_j),\qquad
 m(\gamma_i e)=m(\gamma_j),\qquad
 m(\gamma_i)=m(\gamma_j e).
\]

Because both child cylinders below every \(\gamma_i\) are nonempty, any
two of these three equalities are incompatible.  Thus one scalar chart
contains at most one of these three generators, and at least three charts
are required to cover (1) elementwise.  The allocation above attains that
covering lower bound.

The groups \(K_k\cong A_8\) are perfect but not superperfect.  Instead of
enlarging their leaf sets, take their universal central covers.  For each
\(k\), let

\[
  \eta_k:H_k\twoheadrightarrow K_k,
  \qquad H_k\cong 2.A_8.
\]

The finite group \(H_k\) is superperfect.

## 3. The explicit atlas source

Only two of the three chart groups are needed to generate \(Q\).  The
Steinberg commutator identity

\[
 [q_{ij,a},q_{jk,b}]=q_{ik,ab}
 \qquad(i,j,k\text{ distinct})                            \tag{6}
\]

(with \([x,y]=xyx^{-1}y^{-1}\))

gives, for \(s\in\{e,f\}\),

\[
\begin{aligned}
 q_{31,s}&=[q_{32,1},q_{21,s}],&
 q_{32,s}&=[q_{31,1},q_{12,s}],\\
 q_{13,s^*}&=[q_{12,s^*},q_{23,1}],&
 q_{23,s^*}&=[q_{21,s^*},q_{13,1}],\\
 q_{12,1}&=[q_{13,1},q_{32,1}],&
 q_{21,1}&=[q_{23,1},q_{31,1}].
\end{aligned}                                             \tag{7}
\]

Every entry on the right side of (7) belongs to \(K_1\cup K_2\), while
the left sides are precisely the ten generators in (1) allocated to
\(K_3\).  Hence \(\langle K_1,K_2\rangle\) contains all thirty generators
and equals \(Q\).

Define

\[
  P_2=H_1*H_2
  \cong (2.A_8)*(2.A_8).                                 \tag{8}
\]

Map every free factor in (8) through its Schur covering map and then to its
concrete scalar leaf-matrix subgroup of \(Q\).  The induced homomorphism

\[
  \rho:P_2\twoheadrightarrow Q                            \tag{9}
\]

is surjective by (7).  Two is the smallest possible number of finite chart
groups in such a generating atlas, since a single finite subgroup cannot
generate the infinite group \(Q\).

Each free factor is finite and superperfect.  Therefore \(P_2\) is a
finitely generated virtually free superperfect group: its abelianization
is the direct sum of the factor abelianizations, and its second homology is
the direct sum of their second homologies.  Put

\[
  R_2=\ker\rho,\qquad N_2=[P_2,R_2].                      \tag{10}
\]

The standard superperfect-cover form of the universal-central-extension
construction gives

\[
  U_Q\cong P_2/N_2.                                      \tag{11}
\]

Consequently the exact-source character criterion and the one-witness
certificate may be run with the fully specified source (8).  An exact
finite-dimensional representation of this source is nothing more than
two independent exact representations of the one fixed finite group
\(2.A_8\), with one relative conjugating unitary after fixing the basis
for one factor.

One can also choose the survivor explicitly.  For example,

\[
  p_0\in H_2\le P_2,
  \qquad \rho(p_0)=q_{13,1}.                              \tag{12}
\]

The transvections of \(\operatorname{GL}_4(\mathbb F_2)\) form a class of
size \((2^4-1)(2^3-1)=105\).  Under
\(\operatorname{GL}_4(\mathbb F_2)\cong A_8\), this is the class of
fixed-point-free involutions, the products of four disjoint
transpositions.  Their lifts to \(2.A_8\) are involutions: in either
standard Schur double-cover presentation of \(S_8\), four mutually
disjoint transposition lifts have square
\(z^{\binom42}\) times either \(1\) or \(z^4\), hence square to \(1\).
Choose either lift as \(p_0\).  Its image in \(Q\) is nontrivial, so
\(p_0\notin R_2\), and therefore \(p_0\notin N_2\).

## 4. Exact remaining boundary

The group \(P_2\) is finitely presented.  The group
\(U_Q\cong\operatorname{St}_5(L)\) is finitely presented because \(L\) is
a finitely presented unital ring and the Krsti\'c--McCool theorem applies in
rank at least four.  Hence \(N_2\) is finitely normally generated in
\(P_2\).  This proves the existence of a finite list of word constraints

\[
  \mathcal S=\{n_1,\ldots,n_m\}\subseteq N_2.             \tag{13}
\]

The source cited above does **not** print (13) in the two-factor
coordinates.  Extracting such a list requires two effective Tietze steps:

1. write a concrete finite Krsti\'c--McCool presentation of
   \(\operatorname{St}_5(L)\) for the four-generator finite ring
   presentation of \(L\);
2. express its Steinberg generators as words in lifts of the thirty
   elements (1), and translate the presentation across (9), using (7).

Thus the atlas itself, its finite factors, the quotient map, and a survivor
are now explicit.  The finite normal-relator list is known to exist but has
not yet been extracted.  Even after it is extracted, the decisive analytic
question remains whether exact representations of \(P_2\) can make all
words in (13) tend to the identity in normalized Hilbert--Schmidt norm while
keeping (12) a fixed positive distance from the identity.

## 5. Exact negative-rank form

The chosen survivor \(p_0\), lifting \(q_{13,1}\), is an involution.  For
an exact representation \(\pi:P_2\to U(d)\), put

\[
  r_-(\pi)=\dim\ker(\pi(p_0)+1).
\]

The unitary \(\pi(p_0)\) is a self-adjoint involution, and therefore

\[
  \|\pi(p_0)-1\|_{2,d}
  =2\sqrt{\frac{r_-(\pi)}d}.                              \tag{14}
\]

Let \(\|T\|_{\mathrm F}=\operatorname{Tr}(T^*T)^{1/2}\) denote the
unnormalized Frobenius norm.  The tensor-amplified ratio criterion and
(14) give the exact reformulation

\[
\boxed{
 Q\text{ is hyperlinear}
 \iff
 \inf_{\substack{\pi:P_2\to U(d)\\r_-(\pi)>0}}
 \frac{\max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}}
      {\sqrt{r_-(\pi)}}=0.
}                                                           \tag{15}
\]

Indeed, if \(a(\pi)=\|\pi(p_0)-1\|_{2,d}\) and
\(b(\pi)=\max_{n\in\mathcal S}\|\pi(n)-1\|_{2,d}\), then

\[
  \frac{b(\pi)}{a(\pi)}
  =\frac{\max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}}
         {2\sqrt{r_-(\pi)}}.                              \tag{16}
\]

Thus the ambient dimension cancels completely.  A construction proving the
main problem false needs relation-defect energy
\(o(\sqrt{r_-(\pi)})\).  The opposite conclusion would follow from one
constant \(c>0\) such that every exact representation satisfies

\[
  \max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}
  \ge c\sqrt{r_-(\pi)}.                                   \tag{17}
\]

In particular, a dimension-independent Frobenius-stability theorem for
\(U_Q\), correcting the finite presentation to its only
finite-dimensional representation (the trivial one), would imply (17).
Conversely, violations of every estimate (17) give (15), hence make the
already nonsofic group \(Q\) hyperlinear.  Formula (15) is the exact
active-eigenspace interface between the two outcomes; it does not establish
either one.

## 6. Exactification of the Schur-center stratum

Let \(z_i\) be the central involution of \(H_i\cong2.A_8\).  Since the
covering maps kill \(z_i\), both \(z_1,z_2\) belong to \(R_2\).  Define

\[
 C_0=\left\langle\!\left\langle
       [z_1,h]\ (h\in H_2),\ [z_2,h]\ (h\in H_1)
     \right\rangle\!\right\rangle_{P_2}.
\]

Then \(C_0\le [P_2,R_2]=N_2\).  Moreover

\[
 U_0:=P_2/C_0
\]

is the universal central extension of \(A_8*A_8\).  Indeed, every central
extension of \(A_8*A_8\) restricts over each free factor; the universal
property of \(2.A_8\to A_8\) gives unique lifts of both factors, and the
two lifted Schur centers are central, so the induced map from
\((2.A_8)*(2.A_8)\) kills exactly the cross-center commutators above.
This also proves uniqueness of the resulting lift.  Equivalently, the
central kernel is

\[
 H_2(A_8*A_8,\mathbb Z)
 \cong H_2(A_8,\mathbb Z)^{\oplus2}
 \cong (\mathbb Z/2)^{2}.
\]

The group \(U_0\) is a finite central extension of the virtually free group
\(A_8*A_8\), hence is itself virtually free.  In particular, it is
normalized-Hilbert--Schmidt stable.

This makes the Schur-center constraints exact without losing the desired
certificate.  Starting with a ratio sequence for (15), tensor amplification
first gives a sequence with fixed positive displacement of \(p_0\) and
vanishing \(N_2\)-defect.  In particular, the finite defining
cross-center relations of \(U_0\) vanish.  Stability of \(U_0\) corrects
the sequence to exact finite-dimensional representations of \(U_0\).
The correction tends to zero on the fixed generators, so the displacement
of \(p_0\) remains positive and every fixed word from \(N_2/C_0\) still
tends to the identity.  Conversely, such exact \(U_0\)-representations are
already exact \(P_2\)-representations.  Thus the fixed-separation atlas
certificate is equivalent to one in which both Schur centers are exactly
central from the start.

Every exact representation of \(U_0\) splits into the four joint central
characters

\[
 (\pi(z_1),\pi(z_2))=(\varepsilon_1 I,\varepsilon_2 I),
 \qquad \varepsilon_i\in\{1,-1\}.
\]

At least one sector retains a certificate.  Indeed, squared normalized
Hilbert--Schmidt norms are weighted sums over these four orthogonal
sectors.  If the total survivor displacement is at least \(\varepsilon\),
one sector contributes at least \(\varepsilon^2/4\) to its square.  Its
dimension weight is then at least \(\varepsilon^2/16\), while its own
survivor displacement is at least \(\varepsilon/2\); restriction to that
sector therefore preserves vanishing normalized relator defects.  Passing
to a subsequence fixes the same sign pair.  The constructive search may
accordingly be performed in one of four exact central-sign sectors.

## 7. Quantitative normal generation by the survivor

The survivor in (12) is quantitatively complete.  Put

\[
 q_0=q_{13,1}=\rho(p_0).
\]

**Proposition.**  Every generator \(q_{ij,a}\) in (1) is a product of two
conjugates of \(q_0\) in \(Q\).  Consequently, if \(\varphi:Q\to M\) is a
homomorphism into a group equipped with a bi-invariant metric \(d\), then

\[
 \max_{i\ne j,\ a\in S\cup\{1\}}
 d(\varphi(q_{ij,a}),1)
 \le 2d(\varphi(q_0),1).                                \tag{18}
\]

**Proof.**  Choose \(k\) distinct from \(i,j\).  The Steinberg relation
gives

\[
 q_{ij,a}=[q_{ik,a},q_{kj,1}].                          \tag{19}
\]

All scalar unit transvections \(q_{uv,1}\), \(u\ne v\), are conjugate
inside the scalar subgroup
\(\operatorname{GL}_3(\mathbb F_2)\le Q\): permutation matrices send one
ordered pair of coordinates to any other, and in characteristic two no
sign correction is needed.  Write
\(q_{kj,1}=gq_0g^{-1}\).  Since \(q_0\) is an involution, (19) becomes

\[
 q_{ij,a}
 =(q_{ik,a}g)q_0(q_{ik,a}g)^{-1}\;gq_0g^{-1},
\]

a product of two conjugates of \(q_0\).  Bi-invariance and the triangle
inequality give (18).  \(\square\)

In particular, \(q_0\) normally generates \(Q\), with normal width two on
the displayed generating set.  This strengthens the one-witness reduction:
in any exact metric model of \(Q\), separation of the thirty-generator
window is bounded above by twice the separation of \(q_0\).  The same
statement holds for projective unitary representations after passing to
\(PU(d)\) with its quotient normalized-Hilbert--Schmidt metric.  It does
not by itself construct the required models, but it removes any possible
loss from propagating the chosen survivor to the explicit generating
window.

## 8. One-unitary optimization form

Let \(\widehat H\) be the finite set of irreducible complex representations
of \(H=2.A_8\).  Every exact representation
\(\pi:P_2=H_1*H_2\to U(d)\), after a global conjugation, has the form

\[
 \pi|_{H_1}=\bigoplus_{\sigma\in\widehat H}
                    \sigma^{\oplus m_\sigma},\qquad
 \pi|_{H_2}=U\left(\bigoplus_{\sigma\in\widehat H}
                    \sigma^{\oplus n_\sigma}\right)U^*,  \tag{20}
\]

where \(m_\sigma,n_\sigma\in\mathbb N\), the two displayed dimensions
are equal, and \(U\in U(d)\).  Conversely, every choice in (18) defines an
exact representation of the free product.  Thus, after the finite relator
list \(\mathcal S\) is printed, every numerator in (15) is the Frobenius
norm of an explicit fixed word-polynomial in the entries of the single
matrix \(U\) and \(U^*\).

If \(r_-(\sigma)\) is the multiplicity of \(-1\) for the chosen involution
in the irreducible representation \(\sigma\), then

\[
 r_-(\pi)=\sum_{\sigma\in\widehat H}n_\sigma r_-(\sigma). \tag{21}
\]

After the exactification in Section 6, one fixes
\((\varepsilon_1,\varepsilon_2)\in\{\pm1\}^2\) and restricts
\(m_\sigma\) (respectively \(n_\sigma\)) to irreducibles on which the
central involution acts by \(\varepsilon_1\) (respectively
\(\varepsilon_2\)).

Consequently (15) is exactly a sequence of compact one-unitary
optimizations, indexed only by two finite integer multiplicity vectors.
No approximate factor representations, chart choices, or additional
conjugating matrices remain.  Proving that the infimum of the resulting
ratios is zero settles the main problem negatively; a uniform positive
lower bound proves that the explicit Steinberg cover is nonhyperlinear.

## 9. Canonical regular-\(A_8\) criterion

For deciding hyperlinearity of \(Q\), even the multiplicity vectors and the
four Schur-center sectors can be removed.  Let

\[
 \bar P=K_1*K_2\cong A_8*A_8,
 \qquad \bar\rho:\bar P\twoheadrightarrow Q,
\]

and put \(\bar R=\ker\bar\rho\) and
\(\bar N=[\bar P,\bar R]\).  This source still presents the same universal
central extension:

\[
 \bar P/\bar N\cong U_Q.                                \tag{22}
\]

Indeed, embed each chart \(K_i\cong A_8\) into a uniformly refined scalar
leaf chart \(G_i\cong\operatorname{GL}_{N_i}(\mathbb F_2)\), where
\(N_i\ge5\).  The group \(G_i\) is superperfect.  Therefore the map
\(H_2(K_i,\mathbb Z)\to H_2(Q,\mathbb Z)\) factors through zero.  By the
free-product homology formula,

\[
 H_2(\bar P,\mathbb Z)\longrightarrow H_2(Q,\mathbb Z)
 \quad\text{is zero}.                                   \tag{23}
\]

The five-term sequence identifies
\(\bar R/[\bar P,\bar R]\) with \(H_2(Q,\mathbb Z)\).  The quotient
\(\bar P/\bar N\) is perfect and central over \(Q\).  It is universal:
the pullback of any central extension of \(Q\) to \(\bar P\) has zero
cohomology class by (23), and its splitting is unique because \(\bar P\)
is perfect.  This proves (22).

The same argument shows that the two Schur centers in \(P_2\) map
trivially, rather than merely centrally, in \(U_Q\).  A central extension
of \(Q\) splits uniquely over each superperfect \(G_i\); restricting that
split lift to \(K_i\) and using uniqueness of the lift from \(2.A_8\)
forces its central involution to die.  Thus only the \((+,+)\) sector of
Section 6 can satisfy all the \(N_2\)-relations.

Both \(\bar P\) and \(U_Q\) are finitely presented, so (22) implies that
\(\bar N\) is finitely normally generated in \(\bar P\).  Fix a finite
normal generating set

\[
 \bar{\mathcal S}\subseteq\bar N.                       \tag{24}
\]

Let \(\lambda:A_8\to U(20160)\) be the left regular representation.

**Theorem (canonical regular-atlas criterion).**  The following are
equivalent.

1. \(Q=L_{\mathbb F_2}(1,2)^\times\) is hyperlinear.
2. There are integers \(k_n\ge1\) and unitaries
   \(U_n\in U(20160k_n)\) such that the exact representations
   \(\pi_n:\bar P\to U(20160k_n)\) defined by

   \[
   \begin{aligned}
    \pi_n(h)&=\lambda(h)\otimes I_{k_n} &&(h\in K_1),\\
    \pi_n(h)&=U_n(\lambda(h)\otimes I_{k_n})U_n^*
       &&(h\in K_2)
   \end{aligned}                                        \tag{25}
   \]

   satisfy

   \[
    \max_{s\in\bar{\mathcal S}}
       \|\pi_n(s)-I\|_{2}\longrightarrow0.              \tag{26}
   \]

**Proof of \(1\Rightarrow2\).**  Pull a trace-preserving hyperlinear model
of \(Q\) back along \(\bar\rho\).  Its restrictions to the two finite
factors are approximate representations of \(A_8\).  Finite-group
Hilbert--Schmidt stability corrects them to exact representations
\(\alpha_{i,n}\), allowing \(o(d_n)\) padding and then padding the two
factor models to one common dimension.  This does not change any normalized
Hilbert--Schmidt limit.  For every \(h\ne1\) in either factor,

\[
 \operatorname{tr}(\alpha_{i,n}(h))\longrightarrow0,     \tag{27}
\]

because the finite subgroup embeds in \(Q\) and the hyperlinear trace is
the group trace.

Condition (27) forces the normalized irreducible multiplicities of
\(\alpha_{i,n}\) to converge to Plancherel multiplicities.  Explicitly, if
\(m_{\sigma,n}\) is the multiplicity of
\(\sigma\in\widehat{A_8}\) in a \(d_n\)-dimensional factor
representation, character orthogonality gives

\[
 \frac{m_{\sigma,n}}{d_n}
 \longrightarrow\frac{\dim\sigma}{|A_8|}.               \tag{28}
\]

Replace the whole model by the direct sum of \(|A_8|\) copies.  Its
dimension is \(|A_8|d_n\), while \(d_n\) copies of \(\lambda\) have the
same dimension.  By (28), the two representations have a common
subrepresentation of relative dimension tending to one.  After a unitary
conjugacy they therefore differ on each group element by normalized
Hilbert--Schmidt norm tending to zero.  Perform this replacement
independently on both free factors.  The resulting exact free-product
representation has the form (25), and every fixed word changes by
\(o(1)\).  Since the original pulled-back models kill \(\bar R\), they kill
(24) asymptotically, proving (26).

**Proof of \(2\Rightarrow1\).**  Condition (26) and (22) give a homomorphism

\[
 \Psi:U_Q\cong\bar P/\bar N
       \longrightarrow\prod_\omega U(20160k_n)           \tag{29}
\]

into a tracial matrix ultraproduct.  Choose a transvection \(p\) in the
first factor and an element \(h\) of that factor which does not commute
with \(p\).  Their commutator is nonidentity in \(A_8\), so the regular
representation gives

\[
 \|[\Psi(p),\Psi(h)]-I\|_2
 =\|\lambda([p,h])-I\|_2=\sqrt2.                        \tag{30}
\]

Thus \(\Psi\) is nontrivial.  The universal central extension \(U_Q\) is
quasisimple: it is perfect, its quotient by its center is the simple group
\(Q\), and every proper normal subgroup is central.  Hence
\(\ker\Psi\le Z(U_Q)\).  The image \(W=\Psi(U_Q)\) is hyperlinear and fits
into a central extension

\[
 1\longrightarrow Z(U_Q)/\ker\Psi\longrightarrow W
   \longrightarrow Q\longrightarrow1.
\]

Hyperlinearity passes to central quotients, so \(Q\) is hyperlinear.
\(\square\)

This criterion is the minimal analytic face of the Leavitt route.  The two
finite-factor representations no longer vary at all: every unknown is
contained in the single relative unitary \(U_n\).  Producing (25)--(26)
would make the already nonsofic group \(Q\) hyperlinear and settle the main
problem negatively.

## 10. Scalar flux vanishes: the projective regular-atlas criterion

The identity target in (26) can be weakened to a scalar target.  This is a
pointwise weaker finite-dimensional feasibility problem, but relative
perfectness of the atlas kernel makes the two defects quantitatively
equivalent.  In particular, there is no scalar cocycle or phase obstruction
in the remaining construction.

For \(V\in U(d)\), put

\[
 \ell_{\mathrm{pr}}(V)
   :=\inf_{z\in\mathbb T}\|V-zI\|_2.
\]

**Theorem (projective canonical regular-atlas criterion).**  The following
are equivalent.

1. \(Q=L_{\mathbb F_2}(1,2)^\times\) is hyperlinear.
2. There are integers \(k_n\geq1\) and unitaries
   \(U_n\in U(20160k_n)\) for which the exact representations (25) satisfy

   \[
    \max_{s\in\bar{\mathcal S}}
       \ell_{\mathrm{pr}}(\pi_n(s))\longrightarrow0.    \tag{31}
   \]

In fact, after fixing \(\bar{\mathcal S}\), there is a constant
\(C_{\bar{\mathcal S}}<\infty\) such that every exact representation
\(\pi:\bar P\to U(d)\) satisfies

\[
 \max_{s\in\bar{\mathcal S}}\|\pi(s)-I\|_2
 \leq C_{\bar{\mathcal S}}
       \max_{s\in\bar{\mathcal S}}
          \ell_{\mathrm{pr}}(\pi(s)).                  \tag{31a}
\]

**Proof.**  The forward implication follows from the preceding theorem,
which gives the stronger condition (26).

We first prove (31a).  The kernel \(\bar N\) is relatively perfect:

\[
 \bar N=[\bar P,\bar N].                                \tag{31b}
\]

Indeed, the five-term homology sequence for
\(1\to\bar N\to\bar P\to U_Q\to1\) contains

\[
 H_2(U_Q,\mathbb Z)\longrightarrow
 \bar N/[\bar P,\bar N]\longrightarrow
 H_1(\bar P,\mathbb Z).
\]

The first outer group vanishes because a universal central extension is
superperfect, and the second vanishes because \(A_8*A_8\) is perfect.  This
proves (31b).

For each \(s\in\bar{\mathcal S}\), fix an expression

\[
 s=\prod_{j=1}^{m_s}[p_{s,j},n_{s,j}],
 \qquad p_{s,j}\in\bar P,\quad n_{s,j}\in\bar N.       \tag{31c}
\]

Since \(\bar{\mathcal S}\) normally generates \(\bar N\), also fix an
expression of every \(n_{s,j}\) as a product of \(L_{s,j}\) conjugates of
elements of \(\bar{\mathcal S}^{\pm1}\).  Projective length is
subadditive and conjugacy invariant, so, writing

\[
 \delta=\max_{r\in\bar{\mathcal S}}
               \ell_{\mathrm{pr}}(\pi(r)),
\]

we have \(\ell_{\mathrm{pr}}(\pi(n_{s,j}))\le L_{s,j}\delta\).
If a unitary \(v\) is within \(\varepsilon\) of a scalar, then

\[
 \|[u,v]-I\|_2
  =\|uvu^{-1}-v\|_2\le2\varepsilon                     \tag{31d}
\]

for every unitary \(u\).  Applying (31d) to (31c) and telescoping gives

\[
 \|\pi(s)-I\|_2
 \le2\sum_{j=1}^{m_s}L_{s,j}\delta.
\]

Thus (31a) holds with
\(C_{\bar{\mathcal S}}=2\max_s\sum_jL_{s,j}\).
Condition (31) now implies (26) directly, proving the reverse implication
by the preceding canonical criterion.  \(\square\)

For completeness, there are two independent ways to see why projective
models suffice even without the quantitative relative-perfectness argument.

Assume (31), and let \(d_n=20160k_n\).  Passing from \(U(d_n)\) to
\(PU(d_n)\) and then to a metric ultraproduct gives a homomorphism

\[
 \bar\pi:\bar P\longrightarrow\prod_\omega PU(d_n).
\]

Every element of the finite normal generating set
\(\bar{\mathcal S}\) dies by (31).  Hence its normal closure \(\bar N\)
dies, and (22) gives a homomorphism

\[
 \Phi:U_Q\cong\bar P/\bar N
       \longrightarrow\prod_\omega PU(d_n).            \tag{32}
\]

This homomorphism is nontrivial.  Choose \(p,h\in K_1\) with
\([p,h]\ne1\).  Since a nonidentity element has trace zero in the regular
representation,

\[
 \ell_{\mathrm{pr}}
   \bigl((\lambda([p,h])\otimes I_{k_n})\bigr)=\sqrt2.  \tag{33}
\]

Thus \(\Phi([p,h])\ne1\).  Quasisimplicity of \(U_Q\) now implies
\(\ker\Phi\leq Z(U_Q)\).

It remains to note that every subgroup of the projective ultraproduct in
(32) is hyperlinear.  The adjoint representation

\[
 \operatorname{Ad}:PU(d)\longrightarrow U(M_d(\mathbb C))\cong U(d^2)
\]

is faithful.  With normalized traces and Hilbert--Schmidt norms,

\[
 \begin{aligned}
  \ell_{\mathrm{pr}}(V)^2
    &=2-2|\operatorname{tr}_d(V)|,\\
  \|\operatorname{Ad}(V)-I\|_{2,d^2}^2
    &=2-2|\operatorname{tr}_d(V)|^2.
 \end{aligned}                                          \tag{34}
\]

Consequently

\[
 \ell_{\mathrm{pr}}(V)^2
 \leq \|\operatorname{Ad}(V)-I\|_{2,d^2}^2
 \leq 2\ell_{\mathrm{pr}}(V)^2,                        \tag{35}
\]

so the adjoint representations induce an injective homomorphism from the
projective metric ultraproduct into a tracial matrix ultraproduct.  The
image \(J=\Phi(U_Q)\) is therefore hyperlinear.  Since
\(\ker\Phi\leq Z(U_Q)\), the group \(J\) is a central extension of \(Q\).
Thom's central-quotient permanence gives that \(Q\) is hyperlinear.

There is also a constructive proof which stays inside the canonical atlas.
The diagonal tensor-square of the regular representation satisfies

\[
 \lambda\otimes\overline\lambda
   \cong \lambda^{\oplus |A_8|}.                        \tag{36}
\]

Indeed, its character is \(|A_8|^2\) at the identity and zero elsewhere,
which is \(|A_8|\) times the regular character.  Equivalently, on
\(\ell^2(A_8\times A_8)\) the change of variables
\((x,y)\mapsto(x,x^{-1}y)\) conjugates the diagonal left action to the
regular action on the first coordinate and the trivial action on the
second.

Fix once and for all a unitary \(W\) implementing (36).  From a canonical
model \(\pi_n\) in (25), form

\[
 \pi_n^\#=W(\pi_n\otimes\overline{\pi_n})W^*.
\]

On each factor this is again a regular amplification.  Its multiplicity is

\[
 k_n'=|A_8|k_n^2=20160k_n^2,                            \tag{37}
\]

and its one relative unitary is obtained by conjugating
\(U_n\otimes\overline{U_n}\) by the fixed regular intertwiner \(W\).
If \(z\in\mathbb T\) and \(\|\pi_n(s)-zI\|_2\leq\delta\), expansion of
\((zI+E)\otimes(\bar zI+\bar E)-I\) gives

\[
 \|\pi_n^\#(s)-I\|_2\leq2\delta+\delta^2.              \tag{38}
\]

Thus (31) directly produces (26), without passing to an ultraproduct or
invoking central-quotient permanence.  Formulae (36)--(38) are an explicit
phase-clearing operation on the final one-unitary optimization.

In particular, no choice of compatible scalar phases is needed.  More
strongly, (31a) says that asymptotic scalarity of the finitely many matrices
\(\pi_n(s)\) forces asymptotic identity at the same dimension.  The adjoint
and conjugate-tensor arguments remain useful general phase-clearing
mechanisms, but the relatively perfect Leavitt atlas has no persistent
scalar flux for them to remove.

The target is equivalently a scalar trace optimization.  For \(k\geq1\)
define

\[
 \alpha_k=max_{U\in U(20160k)}
   \min_{s\in\bar{\mathcal S}}
   \left|\operatorname{tr}_{20160k}(\pi_U(s))\right|,    \tag{39}
\]

where \(\pi_U\) is the representation (25).  The maximum exists by
compactness.  Formula (34) gives the exact equivalence

\[
 \boxed{\quad Q\text{ is hyperlinear}
   \quad\Longleftrightarrow\quad
   \sup_{k\geq1}\alpha_k=1.\quad}                       \tag{40}
\]

Moreover,

\[
 \alpha_k<1\qquad\text{for every fixed }k.              \tag{41}
\]

Indeed, equality in (39) would make every \(\pi_U(s)\) scalar and would
give a nontrivial finite-dimensional projective representation of \(U_Q\):
nontriviality again follows from the regular first chart.  Composing it
with \(\operatorname{Ad}:PU(20160k)\to U((20160k)^2)\) would give a
nontrivial finite-dimensional unitary representation of \(U_Q\), contrary
to its minimal almost periodicity.  Thus the unresolved issue is the exact
asymptotic behavior of a sequence of strictly subunit compact maxima:

\[
 1-\alpha_k>0\text{ for every }k,
 \qquad
 \inf_k(1-\alpha_k)\stackrel{?}=0.                     \tag{42}
\]

An affirmative answer to (42) is a complete negative solution of
hyperlinear-versus-sofic.

This trace gap is quantitatively equivalent, at the same multiplicity, to
the original ordinary relator gap.  Define

\[
 d_k=\min_{U\in U(20160k)}
       \max_{s\in\bar{\mathcal S}}\|\pi_U(s)-I\|_2.
\]

The trace formula in (34) gives

\[
 \min_U\max_s\ell_{\mathrm{pr}}(\pi_U(s))
 =\sqrt{2(1-\alpha_k)}.
\]

Since projective distance is at most distance to the identity, while
(31a) supplies the reverse comparison, one obtains

\[
 \sqrt{2(1-\alpha_k)}\leq d_k
 \leq C_{\bar{\mathcal S}}\sqrt{2(1-\alpha_k)}.         \tag{42a}
\]

Thus every \(d_k\) is positive, and the unresolved assertion is exactly
\(\inf_k d_k=0\).  No dimension change or ultraproduct is needed for this
equivalence.

The ordinary defect floors obey the stronger direct-sum inequality

\[
 (k+l)d_{k+l}^2\leq k d_k^2+l d_l^2.                  \tag{42b}
\]

To prove it, take minimizing canonical models at multiplicities \(k\) and
\(l\) and form their block direct sum.  This is canonical at multiplicity
\(k+l\).  For each relator, squared normalized Hilbert--Schmidt norms split
as the dimension-weighted sum of the two squared norms, and each summand is
bounded by the corresponding maximum defining \(d_k\) or \(d_l\).

Thus \(a_k=kd_k^2\) is subadditive.  Fekete's lemma gives

\[
 \lim_{k\to\infty}d_k^2=\inf_{k\geq1}d_k^2.            \tag{42c}
\]

Consequently there are only two possibilities: either \(d_k\to0\) through
all large multiplicities and \(Q\) is hyperlinear, or \(d_k\) converges to
one positive dimension-free gap.  Sparse good dimensions and oscillatory
behavior cannot occur.

There is an equivalent formulation using one smooth trace potential.  Put
\(m=|\bar{\mathcal S}|\) and define

\[
 \begin{aligned}
 E_k&=\min_U\frac1m\sum_{s\in\bar{\mathcal S}}
                   \|\pi_U(s)-I\|_2^2,\\
 \gamma_k&=\max_U\operatorname{Re}\left(
          \frac1m\sum_{s\in\bar{\mathcal S}}
                   \operatorname{tr}(\pi_U(s))\right).
 \end{aligned}                                         \tag{42d}
\]

The unitary identity
\(\|W-I\|_2^2=2-2\operatorname{Re}\operatorname{tr}(W)\)
gives

\[
 E_k=2(1-\gamma_k),
 \qquad E_k\leq d_k^2\leq mE_k.                        \tag{42e}
\]

Direct sums give

\[
 (k+l)E_{k+l}\leq kE_k+lE_l,
\]

equivalently, \(k\gamma_k\) is superadditive.  Hence

\[
 \lim_{k\to\infty}\gamma_k=\sup_k\gamma_k,
 \qquad
 Q\text{ is hyperlinear}\Longleftrightarrow
 \lim_{k\to\infty}\gamma_k=1.                        \tag{42f}
\]

Each fixed \(\gamma_k<1\), since equality would force every relator matrix
to be the identity and produce a forbidden nontrivial finite-dimensional
representation of \(U_Q\).  Formula (42d) replaces the nonsmooth min--max
problem by the maximum of one real smooth word-trace polynomial on a
compact unitary group.

The compact maxima have a useful amplification calculus.  For all
\(k,l,m\geq1\),

\[
 \alpha_{mk}\geq\alpha_k,
 \qquad
 \alpha_{20160kl}\geq\alpha_k\alpha_l.                 \tag{43}
\]

For the first inequality, amplify a canonical model by \(I_m\); this
preserves every normalized trace.  For the second, tensor optimizers at
levels \(k\) and \(l\).  On each factor the resulting representation is
again a regular amplification because

\[
 \lambda\otimes\lambda
 \cong\lambda^{\oplus20160},
\]

and normalized traces multiply on tensor products.  After the fixed
regular intertwiner, the relative unitary is \(U\otimes V\), so taking the
minimum over \(s\in\bar{\mathcal S}\) gives the second inequality in (43).

In particular, if \(\alpha_{k_j}\to1\) along arbitrary dimensions, set
\(K_j=\operatorname{lcm}(k_1,\ldots,k_j)\).  Then
\(K_j\mid K_{j+1}\) and the first inequality gives

\[
 \alpha_{K_j}\geq\max_{i\leq j}\alpha_{k_i}\longrightarrow1. \tag{44}
\]

Thus a positive solution can always be represented by a coherent
divisibility chain of regular amplifications; incompatible matrix sizes
cannot be the obstruction.

There is an exact finite-dimensional dual alternative.  Enumerate
\(\bar{\mathcal S}=\{s_1,\ldots,s_m\}\), and form the compact trace body

\[
 \mathcal T=\overline{\bigcup_{k\geq1}
   \left\{\bigl(\operatorname{tr}(\pi_U(s_1)),\ldots,
                    \operatorname{tr}(\pi_U(s_m))\bigr):
             U\in U(20160k)\right\}}
 \subseteq\mathbb C^m.                                  \tag{45}
\]

This set is convex.  If \(U\) and \(V\) define canonical models at
multiplicities \(k\) and \(l\), their block direct sum is canonical at
multiplicity \(k+l\), and its trace vector is

\[
 \frac{k}{k+l}t(U)+\frac{l}{k+l}t(V).
\]

Rational convex combinations therefore occur exactly, and closure gives
all real convex combinations.  The set is also invariant under coordinatewise
complex conjugation, by conjugating a canonical model.

**Theorem (trace-body alternative).**  Exactly one of the following holds.

1. \((1,\ldots,1)\in\mathcal T\).  Then \(Q\) is hyperlinear and hence is
   a hyperlinear nonsofic group.
2. There are coefficients \(c_1,\ldots,c_m\in\mathbb C\) and
   \(\eta>0\) such that, for every \(k\geq1\) and every
   \(U\in U(20160k)\),

   \[
    \operatorname{Re}\sum_{j=1}^m c_j
      \left(1-\operatorname{tr}_{20160k}(\pi_U(s_j))\right)
      \geq\eta.                                        \tag{46}
   \]

**Proof.**  Membership of the all-ones vector gives a sequence with
\(\operatorname{Re}\operatorname{tr}(\pi_U(s_j))\to1\) for every \(j\),
and hence

\[
 \|\pi_U(s_j)-I\|_2^2
  =2-2\operatorname{Re}\operatorname{tr}(\pi_U(s_j))\to0.
\]

The canonical criterion applies.  If the all-ones vector is absent, the
strict separation theorem for a point and a compact convex subset of the
finite-dimensional real vector space underlying \(\mathbb C^m\) gives
(46).  The two alternatives are mutually exclusive.  \(\square\)

Thus the constructive route and the obstruction route are finite duals.
The constructive route seeks trace vectors converging to \((1,\ldots,1)\).
The opposite route must prove one fixed dimension-free tracial polynomial
inequality (46); a collection of dimension-dependent or relator-dependent
lower bounds is insufficient.

### Monomial relative unitaries cannot close the gap

Let \(d_k^{\mathrm{mon}}\) be the minimum defining \(d_k\), with the
relative unitary restricted to the monomial subgroup of
\(U(20160k)\).  Then

\[
 \inf_{k\geq1}d_k^{\mathrm{mon}}>0.                    \tag{47}
\]

Suppose otherwise.  Choose monomial canonical models whose full relator
defect tends to zero.  Sending a monomial unitary to its underlying
permutation is a homomorphism.  Under this map, the first regular
\(A_8\)-chart becomes its regular permutation representation, and
monomial conjugacy of the second chart becomes permutation conjugacy.
We therefore obtain exact homomorphisms

\[
 \sigma_n:\bar P=A_8*A_8\longrightarrow
             \operatorname{Sym}(20160k_n).
\]

If a monomial unitary \(V\) has underlying permutation \(\sigma(V)\),
then

\[
 d_{\mathrm{Hamm}}(\sigma(V),1)
 \leq \frac12\|V-I\|_2^2.                            \tag{48}
\]

Indeed, each moved coordinate contributes exactly two to the
unnormalized squared Frobenius norm of \(V-I\), while each fixed
coordinate contributes a nonnegative phase term.  Thus every member of
the finite normal generating set \(\bar{\mathcal S}\) dies in the metric
ultraproduct, and normal generation produces a homomorphism

\[
 \Phi:U_Q=\bar P/\bar N\longrightarrow
       \prod_\omega\operatorname{Sym}(20160k_n).
\]

This homomorphism is nontrivial: a nonidentity element of the first
regular \(A_8\)-chart moves every point.  Quasisimplicity of \(U_Q\)
therefore gives \(\ker\Phi\leq Z(U_Q)\).  Its image is consequently a
countable central extension of \(Q\).  Every such central extension was
proved nonsofic, whereas this image is a subgroup of a permutation metric
ultraproduct and is therefore sofic.  This contradiction proves (47).

Direct sums stay inside the monomial class, so the argument proving
(42b)--(42c) also shows that \((d_k^{\mathrm{mon}})^2\) converges to its
strictly positive infimum.  Diagonal phases cannot repair the classical
permutation obstruction.  Any successful sequence must use relative
unitaries with genuinely delocalized rows; quantum interference is a
necessary feature of a positive construction, not merely one possible
ansatz.

There is a stronger fibrewise version with an explicit bound.  Use the
canonical decomposition

\[
 \mathbb C^{20160k}=\ell^2(A_8)\otimes\mathbb C^k,
\]

and let

\[
 \mathcal W_k=U(k)\wr\operatorname{Sym}(A_8)
 \leq U(20160k)
\]

be the block-monomial subgroup.  Thus an element of \(\mathcal W_k\) may
apply an arbitrary \(k\)-dimensional unitary inside each of the 20,160
regular fibres and then permute those fibres.  If
\(d_k^{\mathrm{blk}}\) is the minimum defining \(d_k\), restricted to
\(\mathcal W_k\), then

\[
 d_k^{\mathrm{blk}}\geq\sqrt{\frac4{20160}}
 =\frac1{\sqrt{5040}}.                                \tag{49}
\]

Projection \(\mathcal W_k\to\operatorname{Sym}(A_8)\) is a
homomorphism.  Both canonical charts are block monomial, and they project
to the regular \(A_8\)-action and a permutation conjugate of it.  Thus a
block-monomial relative unitary defines an exact homomorphism

\[
 \rho_U:\bar P=A_8*A_8\longrightarrow
          \operatorname{Sym}(20160).
\]

At least one \(s\in\bar{\mathcal S}\) has \(\rho_U(s)\neq1\).
Otherwise normal generation would factor \(\rho_U\) through a nontrivial
finite permutation representation of \(U_Q\), nontriviality following
from the first regular chart.  This contradicts minimal almost
periodicity of \(U_Q\).  A nonidentity permutation moves at least two
blocks.  If a block-monomial unitary \(V\) moves a proportion \(h\) of
the blocks, then its diagonal blocks vanish at those positions and

\[
 \|V-I\|_2^2\geq2h.
\]

The selected relator therefore has squared defect at least
\(2(2/20160)=4/20160\), proving (49).

The result is robust.  Set

\[
 F_k(U)=\max_{s\in\bar{\mathcal S}}\|\pi_U(s)-I\|_2.
\]

There is a constant \(L<\infty\), independent of \(k\), for which

\[
 |F_k(U)-F_k(V)|\leq L\|U-V\|_2.                      \tag{50}
\]

Indeed, if \(q_s\) counts the letters from the second free factor in the
fixed reduced word for \(s\), one may take
\(L=2\max_s q_s\): a conjugated second-chart letter changes by at most
\(2\|U-V\|_2\), and products telescope.  Consequently every sequence
with \(F_k(U_k)\to0\) obeys

\[
 \liminf_k\operatorname{dist}_2(U_k,\mathcal W_k)
 \geq\frac1{L\sqrt{5040}}.                            \tag{51}
\]

Any positive construction must therefore stay a fixed normalized-HS
distance from the entire fibrewise unitary wreath-product ansatz.  It must
genuinely mix the regular fibres, rather than merely rotate within and
permute them.

Haar-random mixing lies at the opposite extreme and also fails.  Let
\(U_k\) be Haar distributed in \(U(20160k)\).  For every fixed
nonidentity \(s\in\bar N\), the standard Haar-unitary asymptotic-freeness
theorem gives

\[
 \operatorname{tr}(\pi_{U_k}(s))\longrightarrow0       \tag{52}
\]

in probability, and in fact in \(L^2\).  To see the limiting value, the
deterministic matrices \(\lambda(a)\otimes I_k\) have their fixed regular
trace distribution, and Haar conjugation makes the second copy
asymptotically free from the first.  Both charts embed in \(U_Q\), so a
nonidentity member of \(\bar N\) is a nontrivial reduced word in
\(A_8*A_8\).  Every nonidentity syllable has regular trace zero, and the
free-product trace of the reduced alternating word is therefore zero.

Delete the identity from \(\bar{\mathcal S}\), if it was included; this
does not change its normal closure.  Since \(\bar{\mathcal S}\) is finite,
(52) holds simultaneously for all its members.  It follows that

\[
 \|\pi_{U_k}(s)-I\|_2^2\longrightarrow2
 \quad(s\in\bar{\mathcal S}),
 \qquad F_k(U_k)\longrightarrow\sqrt2.                \tag{53}
\]

Equivalently, the random smooth potential tends to \(0\) and its mean
energy tends to \(2\), while the desired endpoint is potential \(1\) and
energy \(0\).  Generic quantum mixing is thus maximally far from a
certificate.  Together with (51), this pins any possible positive
construction to a structured intermediate regime: uniformly separated
from block-monomial fibre transport, but also far from asymptotic
freeness.

Only the asymptotic-freeness conclusion was used in (52).  Hence the same
no-go statement holds deterministically for every sequence of relative
unitaries that asymptotically liberates the two regular chart algebras, and
for any random ensemble with that property; Haar measure is just the
canonical example.

There is also a no-go theorem for bounded internal noncommutative
complexity.  Write \(n=20160\) and regard

\[
 M_{nk}(\mathbb C)=M_n(\mathbb C)\otimes M_k(\mathbb C).
\]

For \(R\geq1\), let \(\mathcal C_{k,R}\) be the set of relative
unitaries lying in \(U(M_n(D))\), for some unital \(C^*\)-subalgebra
\(D\leq M_k(\mathbb C)\) whose irreducible representations all have
dimension at most \(R\).  Define

\[
 e_R=\min_{1\leq r\leq R}E_r>0.                       \tag{54}
\]

Then

\[
 F_k(U)^2\geq e_R\qquad(U\in\mathcal C_{k,R}).        \tag{55}
\]

Indeed, after unitary conjugacy inside the multiplicity tensor factor,

\[
 D\cong\bigoplus_j\bigl(M_{r_j}(\mathbb C)\otimes
                         I_{\ell_j}\bigr),
 \qquad r_j\leq R,
 \qquad\sum_jr_j\ell_j=k.
\]

Consequently

\[
 U\cong\bigoplus_j(U_j\otimes I_{\ell_j}),
 \qquad U_j\in U(nr_j),
\]

and its canonical atlas model is the corresponding direct sum of
multiplicity-\(r_j\) models.  Hence

\[
 \begin{aligned}
 \frac1{|\bar{\mathcal S}|}\sum_s
       \|\pi_U(s)-I\|_2^2
 &=\sum_j\frac{r_j\ell_j}{k}
      \left(\frac1{|\bar{\mathcal S}|}\sum_s
       \|\pi_{U_j}(s)-I\|_2^2\right)\\
 &\geq\sum_j\frac{r_j\ell_j}{k}E_{r_j}
 \geq e_R.
 \end{aligned}
\]

The maximum squared defect dominates this average, proving (55).
Positivity in (54) follows from the already proved fixed-dimensional
strict inequalities \(E_r>0\).

Combining (55) with the word-Lipschitz estimate (50), every prospective
certificate \(F_k(U_k)\to0\) satisfies, for each fixed \(R\),

\[
 \liminf_k\operatorname{dist}_2
       (U_k,\mathcal C_{k,R})\geq\frac{\sqrt{e_R}}L.   \tag{56}
\]

For \(R=1\), this excludes arbitrary direct-integral mixtures of scalar
\(20160\)-dimensional atlas models: commuting internal block coefficients
cannot help, even when each scalar fibre uses an arbitrary dense unitary.
For general \(R\), it excludes every uniformly subhomogeneous internal
algebra.  A successful construction must therefore develop unbounded
internal noncommutative representation dimension and remain a fixed
normalized-HS distance from each bounded-subhomogeneity stratum.

The conclusion can be sharpened from metric separation to a trace-weighted
escape law.  For an arbitrary relative unitary, let

\[
 D(U)=C^*\{U_{x,y}:x,y\in A_8\}\leq M_k(\mathbb C)
 \cong\bigoplus_j(M_{r_j}(\mathbb C)\otimes I_{\ell_j})
\]

be the algebra generated by its \(n\times n\) block coefficients, and put

\[
 w_R(U)=\sum_{j:r_j\leq R}\frac{r_j\ell_j}{k}.
\]

Retaining only the summands of size at most \(R\) in the calculation above
gives

\[
 F_k(U)^2\geq e_R w_R(U).                             \tag{57}
\]

Thus every sequence with \(F_k(U_k)\to0\) satisfies

\[
 w_R(U_k)\leq\frac{F_k(U_k)^2}{e_R}\longrightarrow0
 \qquad\text{for each fixed }R.                       \tag{58}
\]

The largest internal block merely tending to infinity is not enough:
asymptotically all Hilbert-space weight must escape every bounded matrix
size.  In particular, no positive-density classical, commutative, or
bounded-quantum sector can survive in a certificate.

The commutative case is stable under almost commutation.  Write the
relative unitary as the \(n\times n\) block matrix
\(U=(U_{x,y})\), and let

\[
 \mathcal H(U)=\{\operatorname{Re}U_{x,y},
                  \operatorname{Im}U_{x,y}:x,y\in A_8\}.
\]

These are \(2n^2\) self-adjoint contractions.  Set

\[
 c(U)=\max_{H,K\in\mathcal H(U)}\|[H,K]\|_{2,k}.
\]

Glebsky's simultaneous normalized-Hilbert--Schmidt almost-commuting
theorem, applied to this fixed finite family, supplies a
dimension-independent function \(\omega(t)\to0\) and pairwise commuting
self-adjoint contractions approximating the members of
\(\mathcal H(U)\).  Assemble their real and imaginary parts into
\(A\in M_n(D)\), where \(D\leq M_k(\mathbb C)\) is abelian.  Blockwise
orthogonality gives

\[
 \|A-U\|_{2,nk}\leq C'_n\omega(c(U)).
\]

The operator norm of \(A\) is bounded in terms of the fixed \(n\), so
\(A^*A\) is correspondingly close to \(I\).  Polar decomposition, with
the kernel completed inside the finite-dimensional algebra \(M_n(D)\),
produces a unitary \(V\in U(M_n(D))\) and a fixed constant \(C_n\) such
that

\[
 \operatorname{dist}_{2,nk}(U,\mathcal C_{k,1})
 \leq C_n\omega(c(U)).                                \tag{59}
\]

Combining (59), (55) at \(R=1\), and the word-Lipschitz estimate (50)
gives

\[
 F_k(U)\geq\sqrt{E_1}-LC_n\omega(c(U)).               \tag{60}
\]

It follows that there is \(c_0>0\), independent of the multiplicity, for
which every certificate sequence obeys

\[
 \liminf_k c(U_k)\geq c_0.                            \tag{61}
\]

Thus a positive model must retain an order-one normalized-HS commutator
between some pair of real or imaginary block coefficients.  Its internal
mixing cannot be asymptotically classical even in the weaker
almost-commuting sense.

Finally, the smooth potential has an explicit Euler--Lagrange equation.
For each \(s\in\bar{\mathcal S}\), write its evaluated reduced word as

\[
 W_s(U)=A_{s,0}C_{s,1}A_{s,1}\cdots
        C_{s,q_s}A_{s,q_s},
 \qquad C_{s,l}=UB_{s,l}U^*,
\]

where the \(A_{s,l}\) and \(B_{s,l}\) are fixed chart matrices; empty
endpoint factors are allowed.  Let \(R_{s,l}(U)\) be the cyclic product of
all factors other than the displayed occurrence of \(C_{s,l}\), starting
immediately after it, and set

\[
 G_k(U)=\sum_{s\in\bar{\mathcal S}}\sum_{l=1}^{q_s}
          [C_{s,l},R_{s,l}(U)].                        \tag{62}
\]

For \(X^*=-X\) and \(U_t=e^{tX}U\), differentiation and cyclicity of trace
give

\[
 \left.\frac d{dt}\right|_{t=0}\gamma_k(U_t)
 =\frac1{|\bar{\mathcal S}|}
    \operatorname{Re}\operatorname{tr}(XG_k(U)).      \tag{63}
\]

Indeed, \(\dot C_{s,l}=[X,C_{s,l}]\), while an occurrence \(PCQ\)
contributes

\[
 \operatorname{tr}(P[X,C]Q)=
 \operatorname{tr}(X[C,QP]).
\]

Every maximizing relative unitary consequently satisfies the exact
cyclic-gradient equation

\[
 G_k(U)=G_k(U)^*.                                     \tag{64}
\]

This is also sufficient for first-order stationarity, since
\(\operatorname{Re}\operatorname{tr}(XG)=0\) for every skew-adjoint
\(X\) exactly when \(G\) is self-adjoint.  Equation (64) has degree bounded
only by the fixed relator words and is preserved by amplification and
block direct sum.  It gives a concrete algebraic locus containing all
finite-dimensional optimizers.

There is also an irreducible purification of any positive certificate.
For an arbitrary relative unitary, use the coefficient-algebra
decomposition from (57):

\[
 D(U)\cong\bigoplus_j(M_{r_j}(\mathbb C)\otimes I_{\ell_j}),
 \qquad
 U\cong\bigoplus_j(U_j\otimes I_{\ell_j}).
\]

Writing

\[
 \mathcal E(U)=\frac1{|\bar{\mathcal S}|}
       \sum_s\|\pi_U(s)-I\|_2^2,
\]

one has the exact barycentric identity

\[
 \mathcal E(U)=\sum_j\frac{r_j\ell_j}{k}\mathcal E(U_j). \tag{65}
\]

Some component therefore satisfies
\(\mathcal E(U_j)\leq\mathcal E(U)\).  By the definition of \(D(U)\),
the block coefficients of that component generate the full matrix algebra
\(M_{r_j}(\mathbb C)\).  Since

\[
 \max_s\|\pi_{U_j}(s)-I\|_2^2
 \leq |\bar{\mathcal S}|\mathcal E(U_j),
\]

every certificate can be replaced by a sequence of internally irreducible
components with the same vanishing endpoint.  Their dimensions must tend
to infinity, by the positive fixed-dimensional energies.  Consequently

\[
 \boxed{\begin{aligned}
 Q\text{ is hyperlinear}\quad\Longleftrightarrow\quad&
 \text{there are }r_i\to\infty\text{ and }U_i\in U(20160r_i)\\
 &\text{whose block coefficients generate }M_{r_i}(\mathbb C),\\
 &\max_s\|\pi_{U_i}(s)-I\|_2\to0.
 \end{aligned}}                                      \tag{66}
\]

Thus convex mixing and internal centers can be removed from the
constructive problem; it suffices to search inside one full matrix factor
at every stage.

## 11. Ring-level Leavitt microstates have a uniform trace obstruction

The atlas problem is genuinely a group-representation problem; it cannot be
solved by first approximating the ambient Leavitt algebra in square matrices.
The following is the matrix specialization of the finite-tracial Leavitt
trace floor recorded in the main notebook.  Let
\(X_0,Y_0,X_1,Y_1\in M_d(\mathbb C)\), let
\(\operatorname{tr}_d=d^{-1}\operatorname{Tr}\), and use the associated
normalized Hilbert--Schmidt norm.  Then

\[
 \boxed{\max\bigl\{
 \|X_0Y_0-I\|_2,\ \|X_1Y_1-I\|_2,
 \ \|Y_0X_0+Y_1X_1-I\|_2
 \bigr\}\geq \frac13.}                              \tag{67}
\]

To prove (67), cyclicity of the finite-dimensional trace gives the exact
identity

\[
 \operatorname{tr}_d(Y_0X_0+Y_1X_1-I)
 =1+\operatorname{tr}_d(X_0Y_0-I)
   +\operatorname{tr}_d(X_1Y_1-I).                  \tag{68}
\]

Since \(|\operatorname{tr}_d(Z)|\leq\|Z\|_2\), if all three errors in
(67) were at most \(\delta\), equation (68) and the triangle inequality
would imply \(1\leq3\delta\).  This proves the claim.  Notice that neither
the cross relations nor adjoints nor operator-norm bounds are needed.
The constant is sharp: already in dimension one, take
\(X_0=X_1=1\) and \(Y_0=Y_1=2/3\), for which all three errors equal
\(1/3\).

The defining module-type relations of the binary Leavitt algebra have
exactly the form \(X_iY_i=I\) and
\(Y_0X_0+Y_1X_1=I\) (after matching the standard generators and their
formal adjoints).  Thus they admit no square-matrix normalized-HS
microstates with vanishing error.  The same observation applies to a
finite-dimensional attempt at the corresponding Cuntz relations by taking
\(X_i=Y_i^*\).

This does **not** obstruct hyperlinearity of \(Q=L_{\mathbb F_2}(1,2)^\times\):
a group microstate for the unit group need not extend additively to the
Leavitt algebra.  It does show that any positive atlas certificate must be
intrinsically group-level.  In particular, a construction obtained by
compressing or perturbing finite-dimensional Cuntz/Leavitt generators while
retaining all three core ring relations cannot reach the endpoint in (66).

## 12. Primary sources

H. V. Khanh and V. H. Thanh, *Matrix generators for the unit groups of
\(L_K(1,d)\)*, arXiv:2607.10351, especially Lemmas 2.2--2.3,
Proposition 3.4, Corollary 4.4, and Theorem 5.3.

C. Lassueur and N. Mazza, *Endotrivial modules for the Schur covers of the
symmetric and alternating groups*, for the standard presentations of
\(2^\pm.S_n\), their common restriction \(2.A_n\), and lift orders of
products of disjoint transpositions.

A. Thom, *Examples of hyperlinear groups without factorization property*,
Lemma 3.3 and Remark 3.4, for central-quotient permanence of
hyperlinearity.

B. Collins and C. Male, *The strong asymptotic freeness of Haar and
deterministic matrices*, Theorem 1.4, for the Haar-random atlas calculation
in (52)--(53).

L. Glebsky, *Almost commuting matrices with respect to normalized
Hilbert--Schmidt norm*, Theorem 4, for the simultaneous approximation of a
fixed family of almost commuting self-adjoint matrices used in (59)--(61).
