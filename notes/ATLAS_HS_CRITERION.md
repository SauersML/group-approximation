# The finite-atlas character criterion

This note isolates the normalized Hilbert--Schmidt model-production problem
for the universal central cover of the binary Leavitt unit group.  The point
is that the source of the finite atlas is virtually free and hence
Hilbert--Schmidt stable.  Consequently, no genuinely approximate maps of the
atlas source are needed: all approximation is concentrated in the normal
subgroup defining the quotient.

## 1. General rectification theorem

Let \(P\) be a finitely generated Hilbert--Schmidt stable group, let
\(N\triangleleft P\), and put \(U=P/N\).  Write

\[
  1_N(p)=
  \begin{cases}
  1,&p\in N,\\
  0,&p\notin N.
  \end{cases}
\]

This is the pullback to \(P\) of the regular character of \(U\).

**Theorem (exact-source character criterion).**  The following are
equivalent.

1. \(U\) is hyperlinear.
2. There are finite-dimensional unitary representations
   \(
     \pi_k:P\to U(d_k)
   \)
   such that
   \[
     \operatorname{tr}_{d_k}(\pi_k(p))\longrightarrow 1_N(p)
     \qquad(p\in P).
   \]
3. For every finite set \(F\subset P\) and every \(\varepsilon>0\), there
   is a finite-dimensional unitary representation
   \(
     \pi:P\to U(d)
   \)
   such that
   \[
   \begin{aligned}
     \|\pi(n)-1\|_{2,d}&<\varepsilon
       &&(n\in F\cap N),\\
     |\operatorname{tr}_d(\pi(p))|&<\varepsilon
       &&(p\in F\setminus N).
   \end{aligned}
   \]

Here \(\operatorname{tr}_d=d^{-1}\operatorname{Tr}\) and
\(\|x\|_{2,d}=\operatorname{tr}_d(x^*x)^{1/2}\).

### Proof

Assume first that \(U\) is hyperlinear.  Choose a trace-normalized
hyperlinear model

\[
  \varphi_k:U\longrightarrow U(d_k)
\]

whose multiplicative defects tend to zero and for which

\[
  \operatorname{tr}_{d_k}(\varphi_k(u))\longrightarrow
  \begin{cases}1,&u=1,\\0,&u\ne1.\end{cases}
\]

Pull it back along the quotient map \(q:P\to U\).  Hilbert--Schmidt
stability of \(P\) supplies genuine representations

\[
  \pi_k:P\longrightarrow U(d_k)
\]

which are pointwise \(2\)-norm close to
\(\varphi_k\circ q\).  (It is enough to obtain closeness on a fixed finite
generating set; asymptotic multiplicativity propagates it to each fixed
word.)  Since normalized trace is \(2\)-norm Lipschitz,

\[
  \operatorname{tr}_{d_k}(\pi_k(p))
  \longrightarrow \delta_{q(p),1}=1_N(p).
\]

This proves \(1\Rightarrow2\).  Equivalently, this implication follows from
Gerasimova--Shchepin's theorem that every embeddable character of a finitely
generated virtually free group is a pointwise limit of traces of
finite-dimensional representations.

The implication \(2\Rightarrow3\) is immediate after taking \(k\) large.
For \(n\in N\), use

\[
  \|\pi_k(n)-1\|_{2,d_k}^2
  =2-2\operatorname{Re}\operatorname{tr}_{d_k}(\pi_k(n)).
\]

For \(3\Rightarrow2\), exhaust the countable group \(P\) by finite sets and
diagonalize, replacing the requested tolerance by its square when needed
for the preceding identity.

Finally suppose \(2\) holds.  In the tracial matrix ultraproduct, define

\[
  \Pi(p)=(\pi_k(p))_\omega.
\]

This is a homomorphism because every \(\pi_k\) is a homomorphism.  If
\(n\in N\), then the character limit and the displayed norm identity give
\(\Pi(n)=1\), so \(N\subseteq\ker\Pi\).  If \(p\notin N\), then

\[
  \tau_\omega(\Pi(p))=0,
\]

and hence \(\Pi(p)\ne1\).  Thus \(\ker\Pi=N\), and \(\Pi\) induces an
embedding of \(U=P/N\) into a tracial matrix ultraproduct.  Therefore \(U\)
is hyperlinear.  This proves \(2\Rightarrow1\) and completes the proof.

## 2. Application to the binary Leavitt atlas

Put

\[
  Q=L_{\mathbb F_2}(1,2)^\times
\]

and let \(U_Q\to Q\) be its universal central extension.  Choose finitely
many finite superperfect scalar leaf-matrix subgroups
\(H_1,\ldots,H_s\) which generate \(Q\), and put

\[
  P=H_1*\cdots *H_s,\qquad R=\ker(P\to Q),\qquad
  N=[P,R].
\]

The finite-atlas calculation gives

\[
  U_Q\cong P/N.
\]

The group \(P\) is a finitely generated virtually free group.  By
Gerasimova--Shchepin it is stable for every normalized \(p\)-Schatten norm,
in particular for normalized Hilbert--Schmidt norm.  The theorem therefore
specializes to

\[
\boxed{
U_Q\text{ is hyperlinear}
\iff
1_{[P,R]}\text{ is a pointwise limit of normalized characters of
finite-dimensional representations of }P.
}
\]

Thom's central-quotient theorem implies that \(Q\) is hyperlinear whenever
\(U_Q\) is hyperlinear.  The already proved nonsoficity of \(Q\) would then
answer "is every hyperlinear group sofic?" negatively.  No splitting of
\(U_Q\to Q\) is used or asserted: such a section would force the unstable
kernel \(K_2(5,L)\) to vanish, which is not presently known.

This criterion is strictly sharper than asking for arbitrary approximate
representations of the Steinberg group.  A candidate model may be assumed,
without loss, to have all of the following exact at every finite stage:

* each finite leaf chart is represented exactly;
* the different charts assemble through the free-product universal
  property to one exact representation of \(P\);
* only the quotient condition remains asymptotic, namely
  \(\pi_k(n)\to1\) in normalized \(2\)-norm for \(n\in[P,R]\).

The separating condition is equally explicit: every
\(p\notin[P,R]\) must have normalized trace tending to zero.  Thus the final
model-production problem is a relative character approximation problem for
a fixed virtually free group, not a general almost-multiplication problem.

## 3. The one-witness certificate for the main problem

For the purpose of producing *some* hyperlinear nonsofic group, the regular
character requirement can be weakened substantially.

The universal cover \(U_Q\) is the finitely presented Steinberg group
\(\operatorname{St}_5(L_{\mathbb F_2}(1,2))\), while \(P\) is finitely
presented.  Hence \(N=[P,R]\) is normally generated in \(P\) by a finite set;
fix one such set

\[
  \mathcal S=\{n_1,\ldots,n_m\}\subset N.
\]

**Theorem (one-witness exact-atlas certificate).**  Suppose that there are
finite-dimensional exact representations

\[
  \pi_k:P\longrightarrow U(d_k)
\]

and one element \(g\in P\) such that

\[
  \max_{1\le j\le m}\|\pi_k(n_j)-1\|_{2,d_k}\longrightarrow0
  \tag{A}
\]

but

\[
  \liminf_k\|\pi_k(g)-1\|_{2,d_k}>0.
  \tag{B}
\]

Then a hyperlinear nonsofic group exists.

### Proof

Let \(\Pi:P\to\prod_\omega U(d_k)\) be the homomorphism defined by the exact
representations.  Condition (A) kills the normal closure of
\(\mathcal S\), which is \(N\).  Thus \(\Pi\) factors through a homomorphism

\[
  \overline\Pi:U_Q=P/N\longrightarrow\prod_\omega U(d_k).
\]

Condition (B) makes this homomorphism nontrivial.  Its kernel is therefore a
proper normal subgroup of the quasisimple group \(U_Q\), and so

\[
  \ker\overline\Pi\subseteq Z(U_Q).
\]

Consequently its image is a central quotient of \(U_Q\) which still maps
onto \(Q\).  The image is a subgroup of a tracial matrix ultraproduct, hence
hyperlinear.  Its kernel over \(Q\) is central, so Thom's central-quotient
permanence makes \(Q\) hyperlinear.  Thus the already nonsofic group \(Q\)
itself is a counterexample.  This proof does not need a separate theorem
asserting that all central covers of \(Q\) are nonsofic.

The certificate is independent of the chosen finite normal generating set:
normal generation and exact multiplicativity of each \(\pi_k\) propagate
(A) to every fixed element of \(N\).

Conversely, failure of normalized-HS stability of \(U_Q\) produces such a
sequence.  Pull an instability witness back to \(P\), rectify it using
Hilbert--Schmidt stability of the virtually free group \(P\), and retain a
generator on which it stays away from the only genuine
finite-dimensional representation of \(U_Q\), namely the trivial one.
Thus the open analytic bit can be stated entirely inside the exact
finite-dimensional representation theory of \(P\).

This is weaker than the regular-character criterion in exactly the useful
direction: no trace-zero condition is imposed on all words outside \(N\);
one positive-distance witness is enough.

## 4. Finite representation coordinates

The one-witness certificate has no hidden approximate group law.  For each
finite factor \(H_i\), choose representatives

\[
  \widehat H_i=\{\sigma_{i,1},\ldots,\sigma_{i,r_i}\}
\]

of its irreducible complex unitary representations.  Every
\(d\)-dimensional representation of \(P=H_1*\cdots *H_s\) is obtained by
choosing, for each \(i\), nonnegative multiplicities \(m_{i,a}\) satisfying

\[
  \sum_a m_{i,a}\dim\sigma_{i,a}=d,
\]

and a conjugating unitary \(V_i\in U(d)\), and setting

\[
  \pi|_{H_i}
  =
  \operatorname{Ad}(V_i)
  \left(\bigoplus_a \sigma_{i,a}^{\oplus m_{i,a}}\right).
\]

There are no compatibility equations between distinct factors: the free
product universal property assembles these restrictions uniquely.
Consequently (A)--(B) are a sequence of finite matrix-feasibility problems
whose variables are:

* finitely many integer multiplicity vectors, one for each fixed finite
  chart;
* finitely many relative unitaries \(V_i\);
* the common matrix size \(d\).

The objective is the normalized \(2\)-norm of finitely many fixed word maps
\(n_j(V_1,\ldots,V_s)\), subject to keeping one fixed word
\(g(V_1,\ldots,V_s)\) away from the identity.  This is the minimal
model-production face of the Leavitt route.

## 5. Dimension-wise defect gaps

Fix \(p_0\in P\) whose image in \(Q\) is nontrivial, a finite normal
generating set \(\mathcal S\) of \(N\), and \(\varepsilon>0\).  Define

\[
 \delta_d(\varepsilon)=
 \inf_{\substack{\pi\in\operatorname{Hom}(P,U(d))\\
                  \|\pi(p_0)-1\|_{2,d}\geq\varepsilon}}
 \max_{n\in\mathcal S}\|\pi(n)-1\|_{2,d},                 \tag{C}
\]

with value \(+\infty\) when the constraint set is empty.  The representation
space is compact, so the infimum is attained.  For every fixed \(d\),

\[
  \delta_d(\varepsilon)>0.                                 \tag{D}
\]

Otherwise a minimizer with zero defect would kill the normal closure of
\(\mathcal S\), factor through \(U_Q=P/N\), and remain nontrivial on
\(p_0N\).  This contradicts the fact that every finite-dimensional unitary
representation of \(U_Q\) is trivial.

Combining compactness with the one-witness certificate gives

\[
 \boxed{
 Q\text{ is hyperlinear}
 \iff
 \text{there is }\varepsilon>0\text{ with }
 \inf_{d\geq1}\delta_d(\varepsilon)=0.
 }
\]

For the forward implication, rectify a pulled-back regular hyperlinear
model; the \(p_0\)-distance tends to \(\sqrt2\).  For the reverse implication,
choose almost minimizers in (C) and apply the one-witness theorem.  Statement
(D) forces the dimensions of any witnessing sequence to diverge.

Thus each finite level has a genuine positive compactness gap.  The open
problem is precisely whether these positive gaps decay to zero at unbounded
dimension.  Section 4 supplies finite multiplicity and unitary coordinates
for every optimization problem (C).

## 6. Tensor-amplified ratio criterion

The seed representations need not keep \(p_0\) a fixed distance from the
identity.  For an exact finite-dimensional representation \(\pi\) of \(P\),
put

\[
 a(\pi)=\|\pi(p_0)-1\|_2,\qquad
 b(\pi)=\max_{n\in\mathcal S}\|\pi(n)-1\|_2.
\]

Then

\[
 \boxed{
 Q\text{ is hyperlinear}
 \iff
 \inf_{\substack{\pi:P\to U(d),\,d\geq1\\a(\pi)>0}}
 \frac{b(\pi)}{a(\pi)}=0.
 }                                                        \tag{E}
\]

Only the reverse implication needs proof.  Choose \(\pi_k\) with
\(a_k>0\) and \(b_k/a_k\to0\).  Replace it by
\(\pi_k^\#=\pi_k\oplus\overline{\pi_k}\).  This preserves all normalized
\(2\)-distances and makes every normalized character value real:

\[
 \operatorname{tr}(\pi_k^\#(w))
 =1-\frac12\|\pi_k(w)-1\|_2^2.                            \tag{F}
\]

If \(a_k\) is bounded below on a subsequence, the one-witness theorem applies
directly.  Otherwise take \(a_k\to0\), put
\(m_k=\lfloor a_k^{-2}\rfloor\), and set
\(\rho_k=(\pi_k^\#)^{\otimes m_k}\).  Formula (F) gives

\[
 \|\rho_k(p_0)-1\|_2^2
 =2\left(1-(1-a_k^2/2)^{m_k}\right)
 \longrightarrow2(1-e^{-1/2})>0.
\]

For \(n\in\mathcal S\), let
\(x_{k,n}=\|\pi_k(n)-1\|_2^2/2\).  Eventually \(0\leq x_{k,n}\leq1\), and

\[
\begin{aligned}
 \|\rho_k(n)-1\|_2^2
 &=2\left(1-(1-x_{k,n})^{m_k}\right)\\
 &\leq2m_kx_{k,n}
 \leq m_kb_k^2
 \longrightarrow0,
\end{aligned}
\]

because \(\sqrt{m_k}b_k\leq b_k/a_k\to0\).  Thus the tensor powers satisfy
the one-witness certificate.

Criterion (E) permits sparse seeds: the survivor may itself vanish in
normalized \(2\)-norm, provided the finite relation defects vanish at a
strictly faster rate.  Tensor powers convert that relative advantage into
constant separation.

## 7. Exact boundary

Hilbert--Schmidt stability of \(P\) does **not** imply stability of the
epimorphism \(P\to P/N\).  Proving that epimorphism stable would select the
nonhyperlinear side; constructing the characters above would select the
hyperlinear-nonsofic side.  The theorem therefore does not resolve the main
question by itself.

Nor may residual finiteness of \(P\) be used to manufacture the required
characters.  Residual finiteness separates elements of \(P\); here one must
simultaneously make every tested element of \(N\) nearly trivial while
keeping every tested element outside \(N\) trace-invisible.  That is exactly
the quotient trace problem.

## 8. Primary sources

* M. Gerasimova and K. Shchepin, *Virtually free groups are
  \(p\)-Schatten stable*, arXiv:2107.10032, Corollaries 3 and 4.
* H. V. Khanh and V. H. Thanh, *Matrix generators for the unit groups of
  \(L_K(1,d)\)*, arXiv:2607.10351, for generation by scalar leaf-matrix
  subgroups and the unstable-\(K_2\) discussion.
