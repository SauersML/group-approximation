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

## 7. One-unitary optimization form

Let \(\widehat H\) be the finite set of irreducible complex representations
of \(H=2.A_8\).  Every exact representation
\(\pi:P_2=H_1*H_2\to U(d)\), after a global conjugation, has the form

\[
 \pi|_{H_1}=\bigoplus_{\sigma\in\widehat H}
                    \sigma^{\oplus m_\sigma},\qquad
 \pi|_{H_2}=U\left(\bigoplus_{\sigma\in\widehat H}
                    \sigma^{\oplus n_\sigma}\right)U^*,  \tag{18}
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
 r_-(\pi)=\sum_{\sigma\in\widehat H}n_\sigma r_-(\sigma). \tag{19}
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

## 8. Primary sources

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
