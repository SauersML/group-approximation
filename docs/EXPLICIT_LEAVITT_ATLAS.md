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

## 2. Refinement into finite superperfect charts

For a leaf set \(D\) and \(r\ge0\), let

\[
  D^{(r)}=\{\delta\mu:\delta\in D,
                         \ \mu\in\{e,f\}^r\}.
\]

This is the uniform depth-\(r\) refinement of \(D\), of cardinality
\(|D|2^r\).  Lemma 2.3 gives

\[
  \alpha\beta^*
   =\sum_{\mu\in\{e,f\}^r}(\alpha\mu)(\beta\mu)^*.
                                                               \tag{4}
\]

The uniform refinement (4) shows that the generator belongs to scalar
charts of arbitrarily large suitable ranks.  A much smaller common atlas is
available.  For \(k\in\{1,2,3\}\), let

\[
  D_k=(C\setminus\{\gamma_k\})
      \cup\{\gamma_ke,\gamma_kf\}.                        \tag{5}
\]

This is a four-leaf set.  The thirty generators distribute among these
three charts as follows:

* \(q_{ij,e}\) and \(q_{ij,f}\) belong to the \(D_i\)-chart;
* \(q_{ij,e^*}\) and \(q_{ij,f^*}\) belong to the \(D_j\)-chart;
* \(q_{ij,1}\) belongs to the \(D_k\)-chart for the unique
  \(k\notin\{i,j\}\).

Every leaf of a fixed \(D_k\) occurs as a row or column endpoint among the
generators allocated to that chart, so no single leaf can be split while
retaining the whole scalar chart.  Uniformly refine all four leaves once:

\[
  D_k^{(1)}=\{\delta e,\delta f:\delta\in D_k\}.
\]

Equation (4) identifies the entire scalar \(D_k\)-chart with the diagonal
copy \(M\mapsto M\otimes I_2\) in the eight-leaf chart.  In particular,
every generator allocated above remains in that common refined chart.  Let

\[
  H_k\cong\operatorname{GL}_8(\mathbb F_2)\le Q
\]

be the resulting scalar leaf-matrix subgroup.  The allocation above shows
that \(H_1,H_2,H_3\) together contain all thirty generators (1).  Moreover,

\[
  \operatorname{GL}_8(\mathbb F_2)
  =\operatorname{SL}_8(\mathbb F_2)
  =\operatorname{PSL}_8(\mathbb F_2).
\]

This finite group is nonabelian simple and has trivial Schur multiplier;
hence it is superperfect.

## 3. The explicit atlas source

Define

\[
  P_3=H_1*H_2*H_3
  \cong *^3\operatorname{GL}_8(\mathbb F_2).              \tag{6}
\]

Map every free factor in (6) to its concrete scalar leaf-matrix subgroup
of \(Q\).  The induced homomorphism

\[
  \rho:P_3\twoheadrightarrow Q                            \tag{7}
\]

is surjective because its image contains all the generators (1).

Each free factor is finite and superperfect.  Therefore \(P_3\) is a
finitely generated virtually free superperfect group: its abelianization
is the direct sum of the factor abelianizations, and its second homology is
the direct sum of their second homologies.  Put

\[
  R_3=\ker\rho,\qquad N_3=[P_3,R_3].                       \tag{8}
\]

The standard superperfect-cover form of the universal-central-extension
construction gives

\[
  U_Q\cong P_3/N_3.                                       \tag{9}
\]

Consequently the exact-source character criterion and the one-witness
certificate may be run with the fully specified source (6).  An exact
finite-dimensional representation of this source is nothing more than
three independent exact representations of the one fixed finite group
\(\operatorname{GL}_8(\mathbb F_2)\), with two relative conjugating
unitaries after fixing the basis for one factor.

One can also choose the survivor explicitly.  For example,

\[
  p_0=q_{12,1}\in H_3\le P_3.                             \tag{10}
\]

Its image in \(Q\) is nontrivial, so \(p_0\notin R_3\), and therefore
\(p_0\notin N_3\).

## 4. Exact remaining boundary

The group \(P_3\) is finitely presented.  The group
\(U_Q\cong\operatorname{St}_5(L)\) is finitely presented because \(L\) is
a finitely presented unital ring and the Krsti\'c--McCool theorem applies in
rank at least four.  Hence \(N_3\) is finitely normally generated in
\(P_3\).  This proves the existence of a finite list of word constraints

\[
  \mathcal S=\{n_1,\ldots,n_m\}\subseteq N_3.              \tag{11}
\]

The source cited above does **not** print (11) in the three-factor
coordinates.  Extracting such a list requires two effective Tietze steps:

1. write a concrete finite Krsti\'c--McCool presentation of
   \(\operatorname{St}_5(L)\) for the four-generator finite ring
   presentation of \(L\);
2. express its Steinberg generators as words in lifts of the thirty
   elements (1), and translate the presentation across (7).

Thus the atlas itself, its finite factors, the quotient map, and a survivor
are now explicit.  The finite normal-relator list is known to exist but has
not yet been extracted.  Even after it is extracted, the decisive analytic
question remains whether exact representations of \(P_3\) can make all
words in (11) tend to the identity in normalized Hilbert--Schmidt norm while
keeping (10) a fixed positive distance from the identity.

## 5. Exact negative-rank form

The chosen survivor \(p_0=q_{12,1}\) is an involution.  For an exact
representation \(\pi:P_3\to U(d)\), put

\[
  r_-(\pi)=\dim\ker(\pi(p_0)+1).
\]

The unitary \(\pi(p_0)\) is a self-adjoint involution, and therefore

\[
  \|\pi(p_0)-1\|_{2,d}
  =2\sqrt{\frac{r_-(\pi)}d}.                              \tag{12}
\]

Let \(\|T\|_{\mathrm F}=\operatorname{Tr}(T^*T)^{1/2}\) denote the
unnormalized Frobenius norm.  The tensor-amplified ratio criterion and
(12) give the exact reformulation

\[
\boxed{
 Q\text{ is hyperlinear}
 \iff
 \inf_{\substack{\pi:P_3\to U(d)\\r_-(\pi)>0}}
 \frac{\max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}}
      {\sqrt{r_-(\pi)}}=0.
}                                                           \tag{13}
\]

Indeed, if \(a(\pi)=\|\pi(p_0)-1\|_{2,d}\) and
\(b(\pi)=\max_{n\in\mathcal S}\|\pi(n)-1\|_{2,d}\), then

\[
  \frac{b(\pi)}{a(\pi)}
  =\frac{\max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}}
         {2\sqrt{r_-(\pi)}}.                              \tag{14}
\]

Thus the ambient dimension cancels completely.  A construction proving the
main problem false needs relation-defect energy
\(o(\sqrt{r_-(\pi)})\).  The opposite conclusion would follow from one
constant \(c>0\) such that every exact representation satisfies

\[
  \max_{n\in\mathcal S}\|\pi(n)-1\|_{\mathrm F}
  \ge c\sqrt{r_-(\pi)}.                                   \tag{15}
\]

In particular, a dimension-independent Frobenius-stability theorem for
\(U_Q\), correcting the finite presentation to its only
finite-dimensional representation (the trivial one), would imply (15).
Conversely, violations of every estimate (15) give (13), hence make the
already nonsofic group \(Q\) hyperlinear.  Formula (13) is the exact
active-eigenspace interface between the two outcomes; it does not establish
either one.

## 6. Primary sources

H. V. Khanh and V. H. Thanh, *Matrix generators for the unit groups of
\(L_K(1,d)\)*, arXiv:2607.10351, especially Lemmas 2.2--2.3,
Proposition 3.4, Corollary 4.4, and Theorem 5.3.

A. Thom, *Examples of hyperlinear groups without factorization property*,
Lemma 3.3 and Remark 3.4, for central-quotient permanence of
hyperlinearity.
