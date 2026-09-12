# Kazhdan heat rounding: theorem boundary and a factorial-trace center countermodel

Date: 2026-09-08.

This note isolates two different questions in the proposed normalized-Hilbert–Schmidt compression argument for \(H=L_{\mathbb F_2}(1,2)^\times\). It does not settle hyperlinearity of \(H\), and it does not disprove conditional-expectation rounding.

## 1. The rounding statement remains an additional hypothesis

For matrices use normalized trace \(\tau_d\), and write

\[
 \|T\|_{\infty\to2}=\sup_{\|x\|\leq1}\|T(x)\|_{2,\tau_d}.
\]

The statement needed is a dimension-independent function \(f(\delta)\to0\) such that every self-adjoint bistochastic completely positive map \(P:M_d\to M_d\) with

\[
 \|P^2-P\|_{\infty\to2}\leq\delta
\]

admits a unital matrix subalgebra \(A\subset M_d\) satisfying

\[
 \|P-E_A\|_{\infty\to2}\leq f(\delta).
\]

The [two-use native rounding reduction](leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md)
now proves that this theorem alone would imply nonhyperlinearity of H.
It constructs the required scalar-global-commutant model by component
selection after the first rounding instance, then uses the second
instance on the isomorphic native subgroup. No separate trace-weight
or factorial-embedding assumption is needed for that conditional
argument. The rounding theorem itself remains unproved.

The following elementary spectral rounding does hold. Regard \(P\) as a self-adjoint contraction on \(L^2(M_d)\), and set \(Q=1_{[1/2,1]}(P)\). For every \(t\in[-1,1]\),

\[
 |t-1_{[1/2,1]}(t)|\leq2|t^2-t|.
\]

Consequently

\[
 \|(P-Q)x\|_2\leq2\|(P^2-P)x\|_2,
 \qquad \|P-Q\|_{\infty\to2}\leq2\delta.
\]

This produces an orthogonal projection, not a proof that its range is a matrix algebra: positivity and complete positivity of \(Q\) have not been established. By contrast, an **exact bistochastic UCP idempotent** is a genuine conditional expectation. If \(a=P(a)\), Schwarz gives \(P(a^*a)\geq a^*a\); trace preservation makes the positive difference zero. The same applies to \(aa^*\), so the multiplicative-domain argument makes the range a subalgebra.

The closest primary result located is [Kitaev, *Almost-idempotent quantum channels and approximate \(C^*\)-algebras*, arXiv:2405.02434v2, §§1.2 and 12.2](https://arxiv.org/html/2405.02434v2). Its hypothesis is \(\|\Phi^2-\Phi\|_{\rm cb}\leq\eta\). Its conclusion gives a finite-dimensional \(C^*\)-algebra \(B\) and UCP maps \(\Delta:B\to M_d\), \(\Upsilon:M_d\to B\) with

\[
 \|\Upsilon\Delta-\mathrm{id}_B\|_{\rm cb}=O(\eta),
 \qquad \|\Delta\Upsilon-\Phi\|_{\rm cb}=O(\eta),
\]

with universal bounds. Section 1.2 explicitly leaves dimension-independent approximation by exact UCP idempotents open. This is a stronger defect norm but a less specialized class of maps; it establishes neither the desired bistochastic \(\infty\to2\) theorem nor a counterexample to it. In particular its approximate factorization must not be quoted as conditional-expectation rounding.

## 2. Exact matrix countermodel to factoriality of the external commutant

Let

\[
 \Gamma=SL_3(\mathbb Z),\qquad K=SL_3(\mathbb F_2),
\]

and choose a nontrivial irreducible unitary representation \(\rho:K\to U(r)\). For odd primes \(p\to\infty\), put \(G_p=SL_3(\mathbb F_p)\) and define the exact representations

\[
 \pi_p(g)=\lambda_{G_p}(g\bmod p)\otimes
 \bigl(1_K^{\oplus r}\oplus\rho\bigr)(g\bmod2)
 \quad\text{on }\mathbb C^{2r|G_p|}.
\]

The reduction map \(\Gamma\to G_p\times K\) is onto. Indeed, the Chinese remainder theorem supplies elementary matrices with any prescribed parameter in either field and parameter zero in the other; elementary matrices generate both field groups.

Write \(D_p=\pi_p(\Gamma)'\). The projection \(e_p\) onto the \(1_K^{\oplus r}\) summand has normalized trace \(1/2\). Moreover

\[
 e_p=\frac1{|K|}\sum_{k\in K}
       \bigl(I_{\ell^2(G_p)}\otimes(1_K^{\oplus r}\oplus\rho)(k)\bigr).
\]

Surjectivity shows that every summand belongs to \(\pi_p(\Gamma)''\). Averaging over \(K\) gives a central projection of this generated finite-dimensional algebra. Thus

\[
 e_p\in Z(D_p),\qquad \tau(e_p)=\tfrac12.
\]

Nevertheless, for every fixed \(g\ne1\), reduction modulo \(p\) is nonidentity for all sufficiently large primes. The normalized regular character of \(G_p\) vanishes there, giving

\[
 \lim_{p\to\infty}\tau(\pi_p(g))=\delta_{g,1}.
\]

Hence the generated algebra in the matricial tracial ultraproduct \(\mathcal M=\prod_\omega M_{2r|G_p|}\) is the canonical \(L(\Gamma)\). This is a factor: a finite conjugacy class in \(SL_3(\mathbb Z)\) would give a finite-index centralizer, which contains a nonzero power of every elementary transvection. Commutation with those powers forces the matrix to be scalar, and the only scalar in \(SL_3(\mathbb Z)\) is the identity.

Property (T) makes the center obstruction persist in the **full external relative commutant**, not just the coordinate commutants. Fix a finite symmetric Kazhdan generating set \(S\), and define the lazy adjoint averages

\[
 T_p=\tfrac12\mathrm{id}
       +\frac1{2|S|}\sum_{s\in S}\operatorname{Ad}\pi_p(s).
\]

These are bistochastic UCP maps, self-adjoint and positive on \(L^2\). Property (T) supplies \(\gamma>0\), independent of \(p\), such that

\[
 \operatorname{spec}(T_p)\subset[0,1-\gamma]\cup\{1\},
 \qquad \ker(1-T_p)=D_p.
\]

The property-(T) spectral-gap principle, including \(SL_m(\mathbb Z)\), \(m\geq3\), is also used in [Ioana, *Almost commuting matrices and stability for product groups*, JEMS 27 (2025), Introduction](https://ems.press/content/serial-article-files/51186).

The uniform gap implies

\[
 \pi(\Gamma)'\cap\mathcal M=\prod_\omega D_p:
\]

any bounded sequence asymptotically commuting with the generators has \(L^2\)-distance tending to zero from its coordinate conditional expectations onto \(D_p\). Therefore

\[
 e=(e_p)_\omega\in
 Z\bigl(\pi(\Gamma)'\cap\mathcal M\bigr),
 \qquad \tau(e)=\tfrac12.
\]

For any integers \(k_p\to\infty\), the finite adjoint-word averages \(P_p=T_p^{k_p}\) satisfy

\[
 \|P_p-E_{D_p}\|_{2\to2}\leq(1-\gamma)^{k_p},
 \qquad \|P_p^2-P_p\|_{\infty\to2}\to0.
\]

Thus exact representations, canonical factorial limiting trace, property (T), and successfully rounded finite Kazhdan averages all coexist with a macroscopic center in the external commutant.

## 3. Scope: this does not refute bounded weight distortion

Let \(\alpha\) run over irreducible representations of \(G_p\), with dimensions \(d_\alpha\). The finite commutant above is

\[
 D_p\cong
 \bigoplus_\alpha M_{r d_\alpha}
 \;\oplus\;
 \bigoplus_\alpha M_{d_\alpha}.
\]

For the first family, the matrix block acts with representation multiplicity \(d_\alpha\); for the second it acts with multiplicity \(r d_\alpha\). Accordingly the ambient matrix trace gives each of the two \(\alpha\)-blocks weight

\[
 w_{\alpha,0}=w_{\alpha,1}
     =\frac{d_\alpha^2}{2|G_p|}.
\]

Define the normalized regular trace on \(D_p\) as the normalized operator trace of left multiplication on the vector space \(D_p\). Since
\(\dim D_p=(r^2+1)|G_p|\), its central block weights are

\[
 \nu_{\alpha,0}=\frac{r^2d_\alpha^2}{(r^2+1)|G_p|},
 \qquad
 \nu_{\alpha,1}=\frac{d_\alpha^2}{(r^2+1)|G_p|}.
\]

Thus the two weight ratios are exactly

\[
 \frac{\nu_{\alpha,0}}{w_{\alpha,0}}
       =\frac{2r^2}{r^2+1},\qquad
 \frac{\nu_{\alpha,1}}{w_{\alpha,1}}
       =\frac2{r^2+1}.
\]

Both are bounded above and away from zero independently of \(p\). The example therefore refutes inference of a factor commutant or one dominant central block from canonical factoriality, but **does not refute a criterion requiring only bounded distortion between ambient and regular central weights**. That is a weaker hypothesis than center triviality and needs its own argument in the \(H\)-specific setting.

Finally, extremality of a limiting trace can support selection of components when the cutting projections asymptotically commute with every generator being modeled. A central projection in the commutant of the subgroup \(L\) need not commute with the native compressor \(u\). Cutting to such a component is therefore not automatically a microstate construction for all of \(H\).

### 3.1. The explicit Ioana model fails uniform heat idempotence

Use the exact algebras and deformation in [Ioana, arXiv:2108.09589](https://arxiv.org/abs/2108.09589), [JEMS version, Notation 6.1 and Lemma 6.2](https://ems.press/content/serial-article-files/51186):

\[
 M_n=M_2^{\otimes n},\quad A_n=(\mathbb C^2)^{\otimes n}\subset M_n,
 \quad\theta=\operatorname{Ad}(U_t^{\otimes n}),
 \quad\rho_t=(1+\cos t)/2.
\]

Here \(U_t=P+e^{it}(1-P)\), with \(P\) the projection onto the antisymmetric line in \(\mathbb C^2\otimes\mathbb C^2\). In the ambient \(M_n\otimes M_n\), define

\[
 F=E_{A_n\otimes1},\qquad G=E_{\theta(A_n\otimes1)},
 \qquad R=(F+G)/2.
\]

These are genuine matrix-algebra conditional expectations. Each is a finite group twirl: the group used in Notation 6.1 generates \(A_n\otimes M_n\), whose commutant is \(A_n\otimes1\). Its conjugate gives \(G\). Thus \(R\) and its powers are finite averages of adjoint unitary maps.

For a Walsh unitary \(x\in A_n\otimes1\) supported on \(\ell\) tensor positions, put \(y=\theta(x)\) and \(a=\rho_t^\ell\). Lemma 6.2 and tensorization give

\[
 Fx=x,\quad Gy=y,\quad Gx=ay,\quad Fy=ax,
 \qquad \langle x,y\rangle=a.
\]

In particular, the conditional expectation onto \(\theta(M_n\otimes1)\) already sends \(x\) to \(ay\in\theta(A_n\otimes1)\), which justifies using the smaller algebra here. Direct calculation now gives

\[
 (R^2-R)x=-\frac{1-a^2}{4}x.
\]

The witnesses are operator-bounded: \(\|x\|=\|x\|_2=1\). Since \(0\leq R\leq1\) on \(L^2\),

\[
 \frac{1-\rho_t^{2n}}4
 \leq\|R^2-R\|_{\infty\to2}\leq\frac14.
\]

Consequently, for \(t\to0\) and \(nt^2\to\infty\), the uniform idempotence defect tends to \(1/4\). This is compatible with the small commutators of the designated length-one Walsh generators in Lemma 6.3; those generators do not test the entire operator unit ball.

There is also an obstruction to repairing this defect by powers **while retaining those generators**. On \(\operatorname{span}\{x,y\}\), the eigenvalues of \(R\) are \(\lambda_\pm=(1\pm a)/2\), and the squared norms of the two components of \(x\) are \(\lambda_\pm\). Therefore

\[
 \|(R^{2k}-R^k)x\|_2^2
 =\sum_{\pm}\lambda_\pm
       [\lambda_\pm^k(1-\lambda_\pm^k)]^2.
\]

Suppose \(k=k_n\geq1\), \(t\to0\), \(nt^2\to\infty\), and \(R^k\) asymptotically fixes the length-one Walsh generators. Their positive eigencomponent forces \(k(1-\rho_t)\to0\), equivalently \(kt^2\to0\). For \(k=1\), take \(\ell=n\). For \(k\geq2\), take the nearest integer to

\[
 \ell_*=
 \frac{\log(2\cdot2^{-1/k}-1)}{\log\rho_t}.
\]

The preceding limits give \(1\leq\ell\leq n\) eventually, and integer rounding changes \(\lambda_+^k\) by \(o(1)\). Thus \(\lambda_+^k\to1/2\), implying

\[
 \liminf\|R^{2k}-R^k\|_{\infty\to2}
 \geq\frac1{4\sqrt2}.
\]

This does not prohibit taking sufficiently large powers that also erase the designated generators.

Both abelian algebras defining \(F,G\) have \(2^n\) equal-rank central blocks, so their ambient and normalized regular central weights agree exactly. The obstruction above is therefore compatible with weight distortion \(1\). Also, the auxiliary expander estimate in Proposition 4.2 controls distance to a tensor subalgebra; it is not a spectral-gap estimate to the full commutant of the packed generators. These distinctions prevent the known non-HS-stability construction from automatically refuting the stronger uniform conditional-expectation rounding problem in §1.

## 4. Near idempotence does give quantitative multiplicative closure

Let \(P:M_d\to M_d\) be bistochastic and UCP, and put

\[
 \varepsilon=\|P^2-P\|_{\infty\to2}.
\]

Self-adjointness is not needed for this section. If \(x\) is a
contraction and \(a=P(x)\), then \(a\) is a contraction and
\(\|P(a)-a\|_2\leq\varepsilon\). Schwarz and trace preservation
give the positive defect

\[
 D_a=P(aa^*)-P(a)P(a)^*\geq0,
 \qquad
 \tau(D_a)=\|a\|_2^2-\|P(a)\|_2^2\leq2\varepsilon.
 \tag{4.1}
\]

The last inequality follows by factoring the difference of the two
squared norms, using their bound by one and
\(\bigl|\|a\|_2-\|P(a)\|_2\bigr|\leq\varepsilon\).

For any contraction \(b\), Stinespring's representation
\(P(c)=V^*\pi(c)V\) gives

\[
 P(ab)-P(a)P(b)
 =V^*\pi(a)(I-VV^*)\pi(b)V.
\]

The second factor \((I-VV^*)\pi(b)V\) has operator norm at most
one. The product of the first factor with its adjoint is \(D_a\).
Taking the trace therefore proves

\[
 \|P(ab)-P(a)P(b)\|_2\leq\sqrt{\tau(D_a)}
 \leq\sqrt{2\varepsilon}.
 \tag{4.2}
\]

The order \(aa^*\) in (4.1) is the left Schwarz defect required
for this product; it has the same trace bound as the \(a^*a\)
defect. Replacing \(P(a)\) by \(a\) in (4.2) yields

\[
 \boxed{\quad
 \|P(ab)-aP(b)\|_2\leq\sqrt{2\varepsilon}+\varepsilon.
 \quad}
 \tag{4.3}
\]

Taking adjoints gives the corresponding right-module estimate. If
also \(b=P(y)\), where \(y\) is a contraction, one obtains

\[
 \boxed{\quad
 \|P(ab)-ab\|_2\leq\sqrt{2\varepsilon}+2\varepsilon.
 \quad}
 \tag{4.4}
\]

Since \(ab\) is a contraction, \(P(ab)\) itself lies in
\(P((M_d)_1)\). Thus (4.4) states uniform approximate
multiplicative closure of the image of the operator unit ball,
with a dimension-independent bound. More generally, for
\(a_j=P(x_j)\), \(\|x_j\|\leq1\), induction using (4.3) gives

\[
 \left\|P(a_1\cdots a_k)-a_1\cdots a_k\right\|_2
 \leq(k-1)\sqrt{2\varepsilon}+k\varepsilon.
 \tag{4.5}
\]

This supplies explicit control for each fixed product length. It
does not give a bound uniform over all words in the algebra
generated by the image, so it does not establish the conditional-
expectation rounding statement in section 1.

## 5. A three-state heat map defeats two direct rounding constructions

The failure of positivity for the spectral cutoff in section 1 can
occur even for actual self-adjoint bistochastic heat maps on
\(M_3\), with idempotence defect tending to zero.

Let \(\mathcal D\subset M_3\) be the diagonal algebra, let
\(S_{12},S_{23}\) be the permutation matrices of the indicated
transpositions, and, for \(0<q<1/4\), define

\[
 \mathcal L_q=(I-E_{\mathcal D})
       +(I-\operatorname{Ad}S_{12})
       +q(I-\operatorname{Ad}S_{23}),\qquad
 t_q=q^{-1/2},\qquad P_q=e^{-t_q\mathcal L_q}.
 \tag{5.1}
\]

Each summand of \(\mathcal L_q\) is positive and self-adjoint on
\(L^2(M_3)\). Its heat semigroup is bistochastic and UCP: each
generator has the form \(c(I-T)\) for a bistochastic UCP map
\(T\), and the usual exponential series, followed by the product
formula for the sum, proves the assertion. Hence \(P_q\) is also
positive as a Hilbert-space operator.

The diagonal and off-diagonal subspaces are invariant. On the
diagonal, \(\mathcal L_q\) is the classical symmetric Markov
generator

\[
 L_q=
 \begin{pmatrix}
  1&-1&0\\
  -1&1+q&-q\\
  0&-q&q
 \end{pmatrix}.
 \tag{5.2}
\]

Its eigenvalues are

\[
 0,\qquad
 \lambda_-(q)=1+q-\sqrt{1-q+q^2},\qquad
 \lambda_+(q)=1+q+\sqrt{1-q+q^2}.
 \tag{5.3}
\]

Here \(\lambda_-(q)\leq3q\), \(\lambda_+(q)\geq1\), and
\(\lambda_-(q)=\tfrac32q+O(q^2)\). On the off-diagonal
subspace, \(\mathcal L_q\geq I\), since \(I-E_{\mathcal D}\)
is the identity there and the remaining terms are positive.
Consequently the off-diagonal heat has \(2\to2\) norm at most
\(e^{-t_q}\). These estimates show

\[
 \|P_q^2-P_q\|_{\infty\to2}
 \leq\|P_q^2-P_q\|_{2\to2}
 \leq\max\{3\sqrt q,e^{-1/\sqrt q}\}
 \longrightarrow0.
 \tag{5.4}
\]

For sufficiently small \(q\), the spectral cutoff
\(F_q=1_{[1/2,1]}(P_q)\) kills the off-diagonal subspace and has
rank two on the diagonal. Its range is
\(\operatorname{span}\{1,v_q\}\), where \(v_q\) is an
eigenvector of \(L_q\) for \(\lambda_-(q)\).

The three coordinates of \(v_q\) are pairwise distinct. Equality
of the first two, or the last two, is excluded by the corresponding
endpoint eigenvector equation and then the other equations. If
the first and third were equal, the two endpoint equations would
give \((1-q)(v_1-v_2)=0\), again forcing a zero eigenvector.

Thus \(F_q\) is not positive. Indeed, if its restriction to
\(\mathbb C^3\) were positive, it would be a unital
trace-preserving positive idempotent and hence a conditional
expectation onto a two-dimensional subalgebra of \(\mathbb C^3\).
Such a subalgebra is constant on the blocks of a two-block
partition. It cannot contain an element with three distinct
coordinates. Equivalently, the cutoff matrix has a negative entry.
This rules out using the exact Hilbert-space cutoff itself as a
conditional expectation, even in this heat example.

A second unsuccessful construction is to take the infinite-time
limit of the same heat. Since \(q>0\), the graph in (5.2) is
connected, and the off-diagonal generator is strictly positive.
Therefore \(\ker\mathcal L_q=\mathbb C1\) and
\(P_q^k\to E_{\mathbb C1}\) as \(k\to\infty\).
Nevertheless this scalar expectation stays far from \(P_q\).

To see both the separation and the existence of a good alternative,
put

\[
 \mathcal B=\{\operatorname{diag}(a,a,b):a,b\in\mathbb C\}.
\]

The slow eigenvector converges, up to normalization and sign, to
\((1,1,-2)\); its heat eigenvalue tends to one. The fast and
off-diagonal heat eigenvalues tend to zero. Hence

\[
 \|P_q-E_{\mathcal B}\|_{2\to2}\longrightarrow0.
 \tag{5.5}
\]

For the unitary \(x=\operatorname{diag}(1,1,-1)\),
\(E_{\mathcal B}x=x\) and
\(\|x-E_{\mathbb C1}x\|_2=2\sqrt2/3\). Thus

\[
 \|P_q-E_{\mathbb C1}\|_{\infty\to2}
 \geq2\sqrt2/3-o(1).
 \tag{5.6}
\]

The example refutes neither existence of a good rounded algebra nor
a dimension-independent rounding theorem: the fixed partition
algebra \(\mathcal B\) is a good approximation by (5.5). It
specifically shows why spectral cutoff and taking powers do not
by themselves supply the required rounding. Together with the
multiplicative estimates in section 4, it leaves the general
rounding question precise and unresolved.

## 6. Canonical Kazhdan microstates can have scalar heat rounding without representation repair

This example concerns \(\Gamma=SL_3(\mathbb Z)\), not the native
group \(H\). It shows that repairing approximate group representations
to exact representations is a strictly stronger demand than rounding
their adjoint heat maps to conditional expectations.

Fix a finite symmetric generating list \(S\) of \(\Gamma\), with
inverse-paired spellings. Property (T), cited in section 2, supplies
\(C_K>0\) such that in every unitary representation

\[
 \operatorname{dist}(\xi,\mathcal H^\Gamma)
 \leq C_K\max_{s\in S}\|s\xi-\xi\|.
 \tag{6.1}
\]

### 6.1. Exact irreducible representations and rank-one compression

For primes \(p\to\infty\), the action of \(SL_3(\mathbb F_p)\)
on the \(p^2+p+1\) points of \(\mathbb P^2(\mathbb F_p)\)
is doubly transitive: lift two distinct lines to independent vectors,
extend to bases, and adjust the third basis vector to make the
change of basis have determinant one. The complex permutation
representation therefore splits as the constants and one irreducible
representation \(\rho_p\) of dimension

\[
 d=p^2+p.
\]

Indeed, double transitivity makes the commutant of the permutation
representation two-dimensional; after its single trivial summand,
only one irreducible summand of multiplicity one remains. Compose
\(\rho_p\) with reduction from \(\Gamma\).

Set \(m=d-1\), and choose an isometry
\(J:\mathbb C^m\to\mathbb C^d\). Let \(V_s\in U(m)\)
be a unitary polar completion of \(J^*\rho_p(s)J\), choosing
\(V_{s^{-1}}=V_s^*\). Since

\[
 I-(J^*\rho_p(s)J)^*(J^*\rho_p(s)J)
 =J^*\rho_p(s)^*(I-JJ^*)\rho_p(s)J
\]

has rank at most one, all but at most one singular value of the
compression equal one. Thus, writing \(\|\cdot\|_F\) for
unnormalized Frobenius norm,

\[
 \|V_s-J^*\rho_p(s)J\|_F\leq1,
 \qquad
 \|\rho_p(s)J-JV_s\|_F\leq\sqrt2.
 \tag{6.2}
\]

The second inequality follows by splitting into the orthogonal
ranges of \(JJ^*\) and \(I-JJ^*\). Word telescoping gives

\[
 \|\rho_p(w)J-JV_w\|_F\leq\sqrt2\,|w|.
 \tag{6.3}
\]

In particular every fixed relation word has normalized HS defect
at most \(\sqrt2|w|/\sqrt m\). Choose one fixed word for each
element of \(\Gamma\); its evaluation defines full asymptotic
homomorphisms \(\Gamma\to U(m)\), not merely solutions of a
selected packet. For any fixed Kazhdan group-algebra SOS certificate,
all its finitely many word-identification defects are consequently
\(O(m^{-1/2})\). The corresponding adjoint SOS residual has the
same \(\infty\to2\) order by
\(\|\operatorname{Ad}W-\operatorname{Ad}Z\|_{\infty\to2}
\leq2\|W-Z\|_2\).

These models have the canonical limiting trace. If \(g\ne1\) in
\(SL_3(\mathbb Z)\), its reduction is nonscalar for all sufficiently
large primes. A nonscalar three-dimensional matrix over
\(\mathbb F_p\) fixes at most \(p+2\) projective points: its
fixed lines lie in its eigenspaces, whose largest possible dimension
is two. The deleted permutation character therefore satisfies

\[
 |\tau_d(\rho_p(g))|\leq\frac1p.
\]

For a fixed representing word \(w\), (6.3) also gives

\[
 |\tau_m(V_w)-\tau_d(\rho_p(g))|
 \leq\frac{\sqrt2|w|}{\sqrt m}+\frac2d.
 \tag{6.4}
\]

Hence \(\tau_m(V_g)\to\delta_{g,1}\).

### 6.2. Uniform scalar rounding of the heat maps

For \(x\in M_m\), put \(X=JxJ^*\). Irreducibility of
\(\rho_p\) and (6.1), applied to its adjoint representation, imply

\[
 \operatorname{var}_d(X)^{1/2}
 \leq C_K\max_s\|[\rho_p(s),X]\|_{2,d}.
\]

Here \(\operatorname{var}_j(z)=\tau_j(z^*z)-|\tau_j(z)|^2\).
The exact variance identity is

\[
 \operatorname{var}_d(JxJ^*)
 =\frac md\operatorname{var}_m(x)
       +\frac m{d^2}|\tau_m(x)|^2.
 \tag{6.5}
\]

Using (6.2) for \(s\) and \(s^{-1}\), lift the matrix
commutator to obtain

\[
 \|[\rho_p(s),JxJ^*]\|_{2,d}
 \leq\sqrt{\frac md}\|[V_s,x]\|_{2,m}
       +\frac{2\sqrt2}{\sqrt d}\|x\|.
\]

Consequently

\[
 \|x-\tau_m(x)I\|_{2,m}
 \leq C_K\max_s\|[V_s,x]\|_{2,m}
       +\frac{2\sqrt2 C_K}{\sqrt m}\|x\|.
 \tag{6.6}
\]

Define the positive adjoint Laplacian and its heat map by

\[
 A_p=I-|S|^{-1}\sum_s\operatorname{Ad}V_s,
 \qquad P_{p,t}=e^{-tA_p}.
\]

For any contraction \(y\), the heat output \(x=P_{p,t}y\)
is a contraction with \(\tau_m(x)=\tau_m(y)\), and

\[
 \langle A_px,x\rangle\leq\frac1{2et},
 \qquad
 \max_s\|[V_s,x]\|_{2,m}^2
 \leq2|S|\langle A_px,x\rangle.
\]

Equation (6.6) proves the dimension-independent rounding estimate

\[
 \boxed{
 \|P_{p,t}-E_{\mathbb C I}\|_{\infty\to2}
 \leq C_K\sqrt{\frac{|S|}{et}}
       +\frac{2\sqrt2 C_K}{\sqrt m}.}
 \tag{6.7}
\]

In particular any \(t_p\to\infty\) gives uniform scalar
expectation rounding. One may take \(t_p=\log m\), which also
satisfies \(t_p\epsilon_p\to0\) for the fixed SOS residual
\(\epsilon_p=O(m^{-1/2})\). The heat maps are bistochastic,
self-adjoint and UCP; (6.7) also forces their uniform idempotence
defects to tend to zero.

### 6.3. Exact representation repair remains impossible

Let \(\sigma:\Gamma\to U(m)\) be any exact representation.
On \(B(\mathbb C^m,\mathbb C^d)\), with Frobenius norm divided
by \(\sqrt m\), let \(\Gamma\) act by
\(T\mapsto\rho_p(g)T\sigma(g)^*\). Its invariant space is
zero: a nonzero intertwiner into the irreducible \(\rho_p\)
would be surjective, contradicting \(m<d\). The vector \(J\)
has norm one, so (6.1) and (6.2) give

\[
 \max_{s\in S}\|\sigma(s)-V_s\|_{2,m}
 \geq C_K^{-1}-\frac{\sqrt2}{\sqrt m}.
 \tag{6.8}
\]

Thus these canonical property-(T) microstates satisfy fixed SOS
residuals and admit scalar heat rounding, while staying uniformly
far from all exact representations in their own dimensions.
An argument demanding ordinary HS representation stability as a
necessary step toward heat-algebra rounding would demand too much.
This example neither proves general rounding from SOS residuals nor
settles the corresponding question for \(H\).

## 7. Schur channels admit dimension-independent linear rounding

There is a positive rounding theorem for the entire Schur class,
including complex correlation matrices. Let \(C=(c_{ij})\) be a
positive semidefinite correlation matrix, and let
\(P_C(x)_{ij}=c_{ij}x_{ij}\). Thus \(P_C\) is bistochastic and
UCP; when \(C\) is real it is also self-adjoint on \(L^2\).
Put \(\delta=\|P_C^2-P_C\|_{\infty\to2}\). Then there is a
partition algebra \(B\), a direct sum of full matrix blocks in
the same coordinate basis, such that

\[
 \boxed{\|P_C-E_B\|_{\infty\to2}
       \leq\frac65\sqrt{201}\,\delta\leq18\delta.}
 \tag{7.1}
\]

Here is a proof without a dimension-dependent net. Set
\(d_{ij}=c_{ij}(1-c_{ij})\). The assignment formula is

\[
 \delta^2=\frac1n\max_{\sigma\in S_n}
                   \sum_i|d_{i,\sigma(i)}|^2.
 \tag{7.2}
\]

Indeed, the squared entry moduli of any contraction form a doubly
substochastic matrix. Completing it to a doubly stochastic matrix
and decomposing the latter into permutation matrices gives the
upper bound, and permutation unitaries attain the maximum.

Fix \(\varepsilon=1/12\). Draw an undirected edge \(ij\)
when \(|d_{ij}|>\varepsilon\). Hermitian symmetry makes this
well-defined, and the diagonal has no such edges. Take a maximal
matching of size \(m\), and delete its endpoint set \(S\).
The permutation swapping its matched pairs gives

\[
 \frac{|S|}{n}=\frac{2m}{n}
       \leq\frac{\delta^2}{\varepsilon^2}.
 \tag{7.3}
\]

Maximality ensures that every pair of retained vertices has
\(|c_{ij}|\,|1-c_{ij}|\leq\varepsilon\). Since
\(|c|+|1-c|\geq1\), each retained coefficient satisfies
exactly one of

\[
 |c_{ij}|\leq2\varepsilon,
 \qquad |1-c_{ij}|\leq2\varepsilon.
 \tag{7.4}
\]

The second alternative defines an equivalence relation. Reflexivity
and symmetry are immediate. For transitivity, represent \(C\)
as the Gram matrix of unit vectors \(v_i\). Two successive high
correlations give \(\|v_i-v_j\|,\|v_j-v_k\|\leq2\sqrt\varepsilon\),
and therefore \(\operatorname{Re}c_{ik}\geq1-8\varepsilon
>2\varepsilon\). The low alternative in (7.4) is impossible,
so the high alternative holds for \(ik\).

Let \(e_{ij}\) be the zero-one equivalence matrix of these
classes, making each deleted vertex its own singleton class.
Its Schur multiplier is the trace-preserving expectation \(E_B\).
On retained pairs, (7.4) gives the sharper defect comparison

\[
 |c_{ij}-e_{ij}|
 \leq\frac{|c_{ij}(1-c_{ij})|}{1-2\varepsilon}
 =\frac65|d_{ij}|.
 \tag{7.5}
\]

Thus, on any contraction input, the retained entries contribute
at most \(36\delta^2/25\) to the squared error. On entries
incident to \(S\), the coefficient error is at most one: all
off-diagonal entries of the partition matrix there are zero,
and its diagonal entries agree with \(C\). Row and column
contraction bounds make the squared contribution at most
\(2|S|/n\leq288\delta^2\). These entry supports are orthogonal
in \(L^2\); adding the bounds proves (7.1).

Consequently Schur channels cannot refute the general rounding
premise. This includes adjoint heat maps built from mutually
commuting unitary matrices, after simultaneous diagonalization.
The proof uses their common
matrix-unit eigenbasis and its assignment formula; no such basis
has been established for the native \(H\)-heat maps.

## 8. Normalized tracial amplification and physical corner localization

[Kalenda--Peralta--Pfitzner, arXiv:2002.12273, Theorem B](https://arxiv.org/html/2002.12273)
states Haagerup's noncommutative little Grothendieck inequality:
for a bounded linear map \(T:A\to\mathcal H\) from a
\(C^*\)-algebra into a Hilbert space, there are states
\(\varphi_1,\varphi_2\) such that

\[
 \|Tx\|^2\leq\|T\|^2
       \bigl(\varphi_1(x^*x)+\varphi_2(xx^*)\bigr).
 \tag{8.1}
\]

Applied to \(T:M_d\to L^2(M_e)\), this proves

\[
 \boxed{\sup_{k\geq1}
   \|\mathrm{id}_{M_k}\otimes T\|_{\infty\to2}
       \leq\sqrt2\,\|T\|_{\infty\to2},}
 \tag{8.2}
\]

where every amplification uses normalized product trace. To see
this, write a contraction \(X\in M_k(M_d)\) as \((x_{ij})\).
Both \(\sum_{ij}x_{ij}^*x_{ij}\) and
\(\sum_{ij}x_{ij}x_{ij}^*\) are at most \(kI\).
Sum (8.1) over the entries and divide by \(k\).

In particular, the near-idempotence defect and the multiplicative
estimates of section 4 remain small uniformly at every normalized
tracial amplification. This does not give the completely bounded
operator-norm hypothesis used in the result cited in section 1.

There is also a physical corner consequence. Let \(Q\) be an
orthogonal projection on \(L^2(M_d)\), with
\(\|Q\|_{\infty\to2}\leq\eta\). Write the states in (8.1)
as \(\varphi_1(x)=\tau(ax)\),
\(\varphi_2(x)=\tau(bx)\), where \(a,b\geq0\) and
\(\tau(a)=\tau(b)=1\). For any \(M>0\), let \(p\)
be the meet of their spectral projections for \([0,M]\).
Then

\[
 \tau(1-p)\leq2/M,
 \qquad
 \|Q C_p\|_{2\to2}=\|C_p Q\|_{2\to2}
       \leq\eta\sqrt{2M},\qquad C_p(x)=pxp.
 \tag{8.3}
\]

The trace estimate is Markov's inequality and subadditivity of
projection trace. For \(x=pxp\), (8.1) and
\(pap,pbp\leq Mp\) give
\(\|Qx\|_2^2\leq2M\eta^2\|x\|_2^2\).
Taking adjoints proves the other operator-norm bound. Choosing
\(M=1/\eta\) loses trace at most \(2\eta\) and makes both
bounds at most \(\sqrt{2\eta}\).

For a self-adjoint channel \(P\) with defect \(\delta\),
its middle spectral projection
\(Q=1_{[a,1-a]}(P)\), \(0<a<1/2\), satisfies
\(\|Q\|_{\infty\to2}\leq\delta/[a(1-a)]\).
Thus (8.3) applies to the unwanted spectral space. It does not
make the remaining spectral projection positive or an algebra.

Nor can physical compression be assumed to preserve idempotence.
For an explicit example, let \(E\) be the expectation onto the
diagonal algebra in the basis
\((e_1+e_d)/\sqrt2,(e_1-e_d)/\sqrt2,e_2,\ldots,e_{d-1}\),
and let \(p=I-e_{dd}\). Although \(E^2=E\) and
\(\tau(p)\to1\),

\[
 C_p E C_p(e_{11})=\tfrac12e_{11}.
 \tag{8.4}
\]

The compressed map has a middle eigenvalue and loses unitality
on \(pM_dp\). An additional algebra-extraction argument is
therefore still required; (8.2)--(8.3) alone do not prove rounding.

## 9. Repairing a known source algebra does not extract the source

[Alekseev--Thom, arXiv:2606.07369, Theorem 3.5](https://arxiv.org/html/2606.07369)
proves dimension-independent normalized-\(L^2\) stability for
contraction-valued approximate unital \(*\)-homomorphisms from
\(M_k\). Its hypotheses control additivity, scalar homogeneity,
multiplication and adjoint uniformly on the source unit ball. The
conclusion allows a small change of the target corner in a
semifinite amplification. It requires an existing exact matrix
source algebra; it is not a near-idempotent-channel theorem.

In the UCP case, the following elementary argument shows exactly
what knowing the source supplies. Let \(B\) be any unital
finite-dimensional \(C^*\)-algebra and \(\phi:B\to M_d\)
be UCP. Suppose

\[
 \sup_{u\in U(B)}
   \tau_d(1-\phi(u)^*\phi(u))\leq\eta.
 \tag{9.1}
\]

Take a finite-dimensional Stinespring dilation
\(\phi(x)=V^*\pi(x)V\), set \(p=VV^*\), and use
\(\operatorname{Tr}/d\) on the dilation space. This trace
normalizes \(p\), not the identity of the whole dilation.
For every \(u\in U(B)\),

\[
 \|[\pi(u),p]\|_{2,\operatorname{Tr}/d}^2
  =2\tau_d(1-\phi(u)^*\phi(u))\leq2\eta.
 \tag{9.2}
\]

Average \(p\) over the compact group \(\pi(U(B))\), obtaining
\(a=E_{\pi(B)'}(p)\), and let \(q=1_{[1/2,1]}(a)\).
Haar averaging and orthogonal projection in Hilbert space give
\(\|p-a\|_2^2\leq\eta\). Spectral rounding makes \(q\)
a nearest projection to \(a\), so
\(\|a-q\|_2^2\leq\|a-p\|_2^2\). Since \(a,q\in\pi(B)'\),
orthogonality also gives

\[
 \|p-q\|_2^2=\|p-a\|_2^2+\|a-q\|_2^2\leq2\eta,
 \qquad
 \left|\frac{\operatorname{rank}q}{d}-1\right|\leq2\eta.
 \tag{9.3}
\]

The rank bound follows from the usual trace formula for two
projections. Because \(q\) commutes with \(\pi(B)\), the map
\(x\mapsto q\pi(x)q\) is an exact representation on \(q\).
For every contraction \(x\in B\), telescoping gives

\[
 \|p\pi(x)p-q\pi(x)q\|_2\leq2\sqrt{2\eta}.
 \tag{9.4}
\]

Thus the known algebra and its full compact unitary group allow
uniform repair with a dimension-independent estimate. They have
not been constructed for the approximate range in section 4.
Applying this argument to \(P\) on its whole source \(M_d\)
would impose a false additional hypothesis, even when \(P\)
is an exact expectation. For instance, if \(P=E_{\mathcal D}\)
and \(u\) is a cyclic permutation matrix in dimension \(d>1\),
then \(P(u)=0\) but \(P(u^*u)=I\). Its multiplicative defect
on that source is one although its idempotence defect is zero.

The positive Schur theorem, tracial amplification bound, and
known-source repair therefore leave one precise missing statement:
find genuine finite algebras \(A_d\subset M_d\) with
\(\|P_d-E_{A_d}\|_{\infty\to2}\to0\) for the native
\(H\)-heat maps. No such construction is claimed here. The
relevant bounded image is \(P_d((M_d)_1)\); a finite-time
heat map's literal linear range is all of \(M_d\).

## 10. A small change of dimension can be removed for expectations

The compression warning in section 8 does not preclude rounding
the compression of an already known exact expectation. In fact,
there is a uniform theorem in this case. Let \(A\subset M_m\)
be a unital finite-dimensional \(*\)-algebra, and let \(p\) have rank
\(n\), with \(\alpha=(m-n)/m\leq1/2\). There exists a unital
algebra \(B\subset pM_mp\) such that, using normalized trace
on this corner,

\[
 \boxed{\|C_pE_AC_p-E_B\|_{\infty\to2,p}
                   \leq25\alpha^{1/4}.}
 \tag{10.1}
\]

The domain in (10.1) is \(pM_mp\), so its rightmost \(C_p\)
is redundant. If \(\alpha=0\), take \(B=A\). Suppose
\(s=m-n\geq1\), and write
\(A=\bigoplus_i(M_{a_i}\otimes I_{b_i})\).

First construct a product-form projection \(p_0\) of rank at
most \(n\). Delete whole represented blocks until the remaining
desired deficit is at most the dimension of the next block.
In that block, remove coordinates in the larger tensor factor,
rounding the deficit upward to a multiple of
\(\min(a_i,b_i)\leq\sqrt m\). Keep all remaining blocks.
The resulting deficit \(d_0=m-\operatorname{rank}p_0\) satisfies

\[
 s\leq d_0\leq s+\sqrt m,\qquad
 \beta=d_0/m\leq\alpha+\sqrt\alpha.
 \tag{10.2}
\]

Each nonzero block of \(p_0\) has the form \(P_i\otimes Q_i\),
so \(p_0Ap_0\) is an algebra. Set
\(A_0=p_0Ap_0\oplus\mathbb C(1-p_0)\). We claim

\[
 \|E_A-E_{A_0}\|_{\infty\to2,m}
                    \leq(\sqrt2+2)\sqrt\beta.
 \tag{10.3}
\]

For a contraction \(x\), its remainder \(x-p_0xp_0\) has
squared \(L^2\)-norm at most \(2\beta\). Its images under
\(E_A\) and \(E_{A_0}\) have norms at most
\(\sqrt{2\beta}\) and \(\sqrt\beta\), respectively; the
second image is scalar on \(1-p_0\).

It remains to compare the maps on \(p_0xp_0\). In a retained
block put \(a'=\operatorname{rank}P\),
\(b'=\operatorname{rank}Q\), and \(\theta=b'/b\).
Writing its corner expectation as \(y\otimes Q\), with
\(\|y\|\leq1\), its full-block expectation is
\(\theta y\otimes I_b\). Their difference therefore has
squared norm, normalized by \(m\), at most

\[
 \frac{a'b'(1-\theta)}m
        \leq\frac{ab-a'b'}m.
 \tag{10.4}
\]

Summing over blocks bounds this last contribution by \(\beta\).
The triangle inequality proves (10.3). The factor \(\theta\)
is essential when the multiplicity space is trimmed: mere
compression of \(E_A\) is then not the corner expectation.

Next rotate \(p_0\) into \(p\). Since
\(p_0\mathbb C^m\cap p\mathbb C^m\) has codimension at
most \(s\) in \(p_0\mathbb C^m\), there is a unitary \(U\)
supported on a subspace of dimension at most \(2s\) such that
\(q=Up_0U^*\leq p\). Consequently
\(\|U-I\|_{2,m}\leq2\sqrt{2\alpha}\).
The \(\infty\to2\) distance between an expectation and its
conjugate is at most \(4\|U-I\|_2\), by telescoping its two
unitary conjugations. Thus the rotation costs at most
\(8\sqrt{2\alpha}\).

Finally let
\(B=U(p_0Ap_0)U^*\oplus\mathbb C(p-q)\), omitting a
zero scalar summand if necessary. Compressing \(E_{UA_0U^*}\)
to \(p\) differs from \(E_B\) only in scalar normalization
on \(p-q\). The squared error in ambient normalized trace is
at most

\[
 \left(\frac{s}{d_0}\right)^2\frac{d_0-s}{m}
           \leq\alpha.
 \tag{10.5}
\]

Combine (10.2)--(10.5) and normalize on \(p\) to get

\[
 \|C_pE_AC_p-E_B\|_{\infty\to2,p}
 \leq
 \frac{(\sqrt2+2)\sqrt{\alpha+\sqrt\alpha}
                 +(8\sqrt2+1)\sqrt\alpha}
      {\sqrt{1-\alpha}}
 \leq25\alpha^{1/4}.
\]

In particular, a heat map on \(M_n=pM_mp\) uniformly close
to \(C_pE_AC_p\), with \(m/n\to1\), already admits
same-dimension expectation rounding. This removes a dimension
matching issue for that precise flexible formulation. It does
not construct the initial algebra \(A\) from near-idempotence.

## 11. Weyl and projective-group diagonal channels also round linearly

Let \(G\) be a finite group, and let \((U_g)_{g\in G}\) be
an orthonormal basis of \(L^2(M_d,\tau_d)\) consisting of unitaries,
with

\[
 U_e=I,\qquad U_gU_h=\sigma(g,h)U_{gh},\qquad
 |\sigma(g,h)|=1.
 \tag{11.1}
\]

In particular \(|G|=d^2\). Suppose a UCP map \(P:M_d\to M_d\)
is diagonal in this basis:
\(P(U_g)=\lambda_gU_g\). It is automatically trace preserving,
because \(\lambda_e=1\) and the other basis elements have trace zero.
The coefficients need not be real; Hilbert-space self-adjointness is
not required. Put \(\delta=\|P^2-P\|_{\infty\to2}\).
If \(0\leq\delta<1/10\), there is a subgroup \(F\leq G\)
such that, for the actual matrix subalgebra
\(B=\operatorname{span}\{U_g:g\in F\}\),

\[
 \boxed{\|P-E_B\|_{\infty\to2}
       \leq\|P-E_B\|_{2\to2}\leq2\delta.}
 \tag{11.2}
\]

The full operator-unit-ball norm detects every spectral defect here.
Indeed, diagonalization gives the \(2\to2\) norm below, and each
unitary basis element attaining its maximum is also an admissible
\(\infty\to2\) test input. Hence

\[
 \delta=\|P^2-P\|_{2\to2}
       =\max_{g\in G}|\lambda_g(1-\lambda_g)|.
 \tag{11.3}
\]

Complete positivity makes \(\lambda\) a positive-definite function
on \(G\), including when the multiplication in (11.1) is twisted.
For any finite list \(g_1,\ldots,g_k\), the operator matrix
\([U_{g_i}^*U_{g_j}]\) is positive. Applying the amplification of
\(P\) gives the positive matrix with entries

\[
 P(U_{g_i}^*U_{g_j})
   =\lambda_{g_i^{-1}g_j}U_{g_i}^*U_{g_j}.
\]

This equality includes the projective phases, since each product is
a scalar multiple of its indexed basis unitary. Conjugating the matrix
by \(\operatorname{diag}(U_{g_i})\) produces
\([\lambda_{g_i^{-1}g_j}I]\geq0\), as required. In particular,
there are unit vectors \(v_g\) with Gram entries
\(\lambda_{g^{-1}h}\), and \(\lambda_e=1\).

Equation (11.3) and
\(|\lambda|+|1-\lambda|\geq1\) show that each coefficient lies
in exactly one of the two disjoint disks

\[
 |\lambda_g|\leq2\delta,
 \qquad |1-\lambda_g|\leq2\delta.
 \tag{11.4}
\]

Let \(F\) consist of the second alternative. It contains the identity
and is invariant under inversion. If \(g,h\in F\), the Gram
distances from \(v_g,v_h\) to \(v_e\) are at most
\(2\sqrt\delta\). Thus

\[
 \operatorname{Re}\lambda_{g^{-1}h}
       \geq1-8\delta>2\delta.
\]

The first disk in (11.4) is excluded, so \(g^{-1}h\in F\).
This proves that \(F\) is a subgroup. By (11.1), its span \(B\)
is a unital \(*\)-subalgebra. Its trace-preserving conditional
expectation is exactly the orthogonal Fourier cutoff
\(E_B(U_g)=1_F(g)U_g\). Finally (11.4) gives (11.2).

This excludes Weyl- and Pauli-diagonal channels as counterexamples to
uniform rounding. In those cases \(G\) is abelian and conjugations
by its projective unitaries are diagonal in the same unitary basis;
their averages and heat maps satisfy the hypotheses. The proof also
allows nonabelian indexing groups when a basis as in (11.1) exists
and the channel is diagonal in it. A general average of conjugations
by a nonabelian unitary group need not have this diagonal form.
No such form has been established for the native \(H\)-heat maps,
so this restricted theorem does not decide hyperlinearity of \(H\).

## 12. Uniformly bounded Kraus rank does give expectation rounding

**Theorem.** Fix \(r\in\mathbb N\). Let \(P_n:M_{d_n}\to M_{d_n}\)
be self-adjoint bistochastic UCP maps admitting at most \(r\) Kraus
operators. If

\[
 \|P_n^2-P_n\|_{\infty\to2}\longrightarrow0,
 \tag{12.1}
\]

then there are unital \(C^*\)-subalgebras \(A_n\subseteq M_{d_n}\)
such that

\[
 \|P_n-E_{A_n}\|_{\infty\to2}\longrightarrow0.
 \tag{12.2}
\]

Equivalently, for each fixed \(r\) and each \(\varepsilon>0\),
there is \(\delta(r,\varepsilon)>0\), independent of \(d\),
such that defect below \(\delta(r,\varepsilon)\) implies distance
below \(\varepsilon\) to an algebra expectation. The proof below
does not give a quantitative modulus in \(r\).

Write, padding the family with zero operators if necessary,

\[
 P_n(x)=\sum_{i=1}^{r}a_{i,n}^*xa_{i,n},\qquad
 \sum_i a_{i,n}^*a_{i,n}=\sum_i a_{i,n}a_{i,n}^*=I.
 \tag{12.3}
\]

In particular \(\|a_{i,n}\|\leq1\). For a finite Kraus family
\(a=(a_i)\) on \(M_d\), form the positive finite-rank operator

\[
 R_a=\sum_i |a_i\rangle\langle a_i|
       \quad\hbox{on }L^2(M_d,\tau_d).
\]

These vectors use normalized matrix trace; the Hilbert--Schmidt
norm of \(R_a\) is the ordinary Hilbert-space operator
Hilbert--Schmidt norm. If \(P_a,P_b\) are the associated CP maps,
Haar averaging gives the exact identity

\[
 \|R_a-R_b\|_{\mathrm{HS}}^2
   =\int_{U(d)}\|(P_a-P_b)(u)\|_{2,d}^2\,du.
 \tag{12.4}
\]

Indeed, the cross term for individual Kraus operators is
\(\int\langle a^*ua,b^*ub\rangle_{2,d}\,du
=|\tau_d(a^*b)|^2\), which is also the cross term for the
rank-one operators in the frames. Thus (12.1) implies

\[
 \left\|R_{(a_{i,n}a_{j,n})_{i,j}}-R_{(a_{i,n})_i}
          \right\|_{\mathrm{HS}}\longrightarrow0.
 \tag{12.5}
\]

The corresponding trace-norm bound is at most
\(\sqrt{r^2+r}\,\|P_n^2-P_n\|_{\infty\to2}\).
Self-adjointness of \(P_n\), applied to (12.4) and its adjoint
Kraus family, also gives the exact equality
\(R_{(a_{i,n}^*)_i}=R_{(a_{i,n})_i}\).

To prove the theorem, suppose a counterexample sequence stayed a
fixed positive distance from every algebra expectation, and take
its tracial ultraproduct \(M=\prod_\omega(M_{d_n},\tau_{d_n})\).
Put \(a_i=(a_{i,n})_\omega\). All frame inner products are finite
expressions in traces of fixed products, so (12.5) and the adjoint
frame equality pass to \(L^2(M)\):

\[
 R_{(a_i a_j)_{i,j}}=R_{(a_i)_i}=R_{(a_i^*)_i}.
 \tag{12.6}
\]

The range of a finite positive frame operator is the span of its
vectors. Consequently

\[
 B:=\operatorname{span}\{a_1,\ldots,a_r\}
      =\operatorname{span}\{a_i a_j:i,j\}=B^*.
\]

The relation \(\sum_i a_i^*a_i=I\) puts the identity in \(B\).
Thus \(B\subset M\) is an actual finite-dimensional unital
\(C^*\)-algebra, with \(\dim B\leq r\). Vanishing Gram
eigenvalues cause no difficulty: they merely lower this dimension.
This is the source-extraction step unavailable for unbounded
Kraus families.

There is also a representation-independent consequence of (12.6).
Choose any fixed linear basis of \(B\). Equality of the frame
operators, for the faithful inner product \(\tau|_B\), is
equality of the matrices of quadratic Kraus coefficients in that
basis. Therefore it remains an equality after applying any
\(*\)-representation of \(B\). In particular, the CP map with
Kraus family \((\pi(a_i))_i\) is exactly idempotent and
self-adjoint in every finite-dimensional representation \(\pi\).
The two sums in (12.3) also remain identities on its support.

Lift a fixed system of matrix units of \(B\) to obtain
\(*\)-homomorphisms

\[
 \pi_n:B\longrightarrow p_nM_{d_n}p_n,\qquad
 \tau_{d_n}(1-p_n)\longrightarrow_\omega0,
 \qquad
 \|\pi_n(a_i)-a_{i,n}\|_{2,d_n}\longrightarrow_\omega0.
 \tag{12.7}
\]

Here the supports \(p_n\) are essential: exact unital embeddings
into the whole \(M_{d_n}\) can fail divisibility conditions.
For completeness, the lifting uses only finitely many matrix
units. Lift their diagonal projections to orthogonal projections;
within each simple block, trim them to the smallest common rank.
Their normalized rank differences tend to zero because the
limiting projections are equivalent. Polar decomposition of the
compressed off-diagonal lifts, completed on their small kernels,
then gives partial isometries with these common supports, and their
products give exact matrix units.
Only \(o_\omega(d_n)\) dimensions are lost. The number and degrees
of the matrix blocks are fixed, so the finitely many corrections
all tend to zero in normalized \(2\)-norm.

Set \(b_{i,n}=\pi_n(a_i)\), \(q_n=1-p_n\), and define

\[
 \widetilde P_n(x)
      =\sum_i b_{i,n}^*xb_{i,n}+q_nxq_n.
 \tag{12.8}
\]

The coefficient identities just established make the first term
exactly idempotent on \(p_nM_{d_n}p_n\). The second term is the
identity channel on the complementary corner, and mixed terms
vanish. Hence \(\widetilde P_n\) is a self-adjoint bistochastic
UCP idempotent. It is the trace-preserving expectation onto its
fixed algebra \(A_n\). Finally, for every contraction \(x\),

\[
 \|P_n(x)-\widetilde P_n(x)\|_{2,d_n}
 \leq2\sum_i\|a_{i,n}-b_{i,n}\|_{2,d_n}
               +\sqrt{\tau_{d_n}(q_n)}
 \longrightarrow_\omega0.
 \tag{12.9}
\]

This uniform bound contradicts the counterexample sequence and
proves both formulations of the theorem.

The fixed-rank hypothesis concerns the channels themselves, not
the number of adjoint generators of their heat semigroup. If
\(T=|S|^{-1}\sum_{s\in S}\operatorname{Ad}(V_s)\), then

\[
 e^{-t(I-T)}=e^{-t}\sum_{k\geq0}\frac{t^k}{k!}T^k.
 \tag{12.10}
\]

For every \(t>0\), all word lengths have positive coefficients.
The support of its Kraus frame is therefore the span of all words
in the \(V_s\), namely \(C^*(V_s:s\in S)\) for an
inverse-paired generator list. Its minimal exact Kraus rank is
the dimension of that algebra, which can grow with \(d\) despite
fixed \(|S|\). Truncation gives finite Kraus approximations, but
their rank bound grows with the truncation length and heat time.

In the native argument the near-idempotence estimate contains a
term decaying like \(e^{-\kappa t}\), while a word truncation
has a rank bound growing like \(|S|^{O(t)}\). A modulus available
separately for each fixed \(r\) does not show that
\(f_{r(t)}(e^{-\kappa t})\to0\). Slowing the matrix-model error
does not remove this linked dependence on \(t\). Thus the theorem
proves rounding for bounded Kraus rank, but neither proves it for
the native heat maps nor settles hyperlinearity of \(H\).

## 13. Canonical long-time heat cannot have asymptotically exact bounded-rank approximations

The rank issue in section 12 is present in the native models, even
if one allows approximation of their heat channels first. Let
\(V_{n,s}\) be full canonical microstates for a finite symmetric
generating list of an infinite group \(G\), with inverse-paired
unitary spellings, and let

\[
 A_n=I-|S|^{-1}\sum_s\operatorname{Ad}V_{n,s},
 \qquad P_n=e^{-t_nA_n},\qquad t_n\longrightarrow\infty.
\]

No SOS error condition on these times is needed in this section.
Define the normalized superoperator purity

\[
 \chi_n^2=\frac{1}{d_n^2}
       \operatorname{Tr}_{L^2(M_{d_n})}(P_n^2).
 \tag{13.1}
\]

Then \(\chi_n\to0\). Moreover, for every bistochastic CP
channel \(Q_n\) with at most \(r\) Kraus operators,

\[
 \boxed{\|P_n-Q_n\|_{\infty\to2}
             \geq r^{-1/2}-\chi_n.}
 \tag{13.2}
\]

In particular, no one fixed Kraus bound permits asymptotically
exact approximation of these heat maps. The statement applies to
both the canonical global \(H\)-heat and its native \(L\)-heat.

To prove the purity limit, fix \(T>0\). For all sufficiently
large \(n\), spectral monotonicity gives

\[
 \chi_n^2\leq\frac1{d_n^2}
       \operatorname{Tr}(e^{-2TA_n}).
 \tag{13.3}
\]

Expand the right side by the Poisson series in (12.10). For each
literal word \(w\),

\[
 \frac1{d_n^2}\operatorname{Tr}(\operatorname{Ad}V_{n,w})
            =|\tau_{d_n}(V_{n,w})|^2.
\]

Canonicality makes this tend to one if \(w\) is the identity
of \(G\), and to zero otherwise. The Poisson tails are bounded
uniformly in \(n\), since each squared normalized trace is at
most one. Thus the right side of (13.3) tends to
\(\mu_{2T}(e)\), the return probability of the continuous-time
walk on \(G\) generated by the uniform measure on \(S\).

As \(T\to\infty\), this return probability tends to zero.
Indeed, the regular-representation heat converges strongly to the
projection onto invariant vectors in \(\ell^2(G)\). Its kernel
consists of functions invariant under every generator, and there
is no nonzero square-summable constant function on an infinite
group. Taking \(T\to\infty\) after the limit in (13.3) proves
\(\chi_n\to0\).

For (13.2), associate to a CP map its Kraus frame \(R_Q\) as
in section 12. For a bistochastic map, \(R_Q\geq0\) and
\(\operatorname{Tr}(R_Q)=1\). If its rank is at most \(r\),
Cauchy--Schwarz on its eigenvalues gives
\(\|R_Q\|_{\mathrm{HS}}\geq1/\sqrt r\).
The Haar identity (12.4) and the triangle inequality yield

\[
 \|P_n-Q_n\|_{\infty\to2}
 \geq\|R_{P_n}-R_{Q_n}\|_{\mathrm{HS}}
 \geq r^{-1/2}-\|R_{P_n}\|_{\mathrm{HS}}.
\]

Haar unitaries are isotropic in normalized \(L^2(M_d)\):
their covariance is \(d^{-2}I\). Consequently
\(\|R_{P_n}\|_{\mathrm{HS}}^2
=d_n^{-2}\operatorname{Tr}(P_n^*P_n)=\chi_n^2\), proving
the claim.

This does not exclude approximation at tolerance \(\eta\)
using a rank bound depending on \(\eta\). It forces such a
bound to grow at least on the order of \(\eta^{-2}\). The
rank-dependent rounding modulus needed to use that possibility
has not been supplied.

### 13.1. Small frame Hilbert--Schmidt defect alone is insufficient

There is also an explicit obstruction to dropping rank control
from the frame argument. On \(M_d\), \(d>1\), let

\[
 P_d=\tfrac12(E_{\mathcal D}+E_{\mathbb C I}),
\]

where \(\mathcal D\) is the diagonal algebra. Then

\[
 P_d^2-P_d=\tfrac14(E_{\mathbb C I}-E_{\mathcal D}),
 \qquad \|P_d^2-P_d\|_{\infty\to2}=\tfrac14.
 \tag{13.4}
\]

The norm is attained by a trace-zero diagonal unitary. If \(E\)
is any algebra expectation, telescoping
\(P_d^2-P_d=P_d(P_d-E)+(P_d-E)E-(P_d-E)\) shows
\(\|P_d-E\|_{\infty\to2}\geq1/12\).

Nevertheless the frame defect tends to zero in Hilbert--Schmidt
norm. The frames of the two expectations are
\(R_{E_{\mathcal D}}=d^{-1}\operatorname{Proj}_{L^2(\mathcal D)}\)
and \(R_{E_{\mathbb C I}}=d^{-2}I\). Hence

\[
 \|R_{P_d^2}-R_{P_d}\|_{\mathrm{HS}}
       =\frac{\sqrt{d-1}}{4d}\longrightarrow0,
 \qquad
 \|R_{P_d^2}-R_{P_d}\|_1
       =\frac{d-1}{2d}\longrightarrow\tfrac12.
 \tag{13.5}
\]

Thus small frame Hilbert--Schmidt defect cannot replace the
uniform channel defect in an unbounded-rank extraction argument.
This example fails the actual near-idempotence hypothesis and is
not a counterexample to the general rounding premise.

## 14. Almost-fixed unitaries exist, but their generated group can escape

One can describe the bounded channel image using almost-fixed
unitaries. Let \(P\) be bistochastic and UCP, with
\(\varepsilon=\|P^2-P\|_{\infty\to2}\). For every
\(x\) with \(\|x\|\leq1\), put \(a=P(x)\). For
\(0<r<1\), there are unitaries
\(u_1,u_2\) such that

\[
 \left\|a-\frac{u_1+u_1^*}{2}
              -i\frac{u_2+u_2^*}{2}\right\|_2\leq r,
 \qquad
 \|P(u_j)-u_j\|_2\leq\sqrt{2\varepsilon/r}.
 \tag{14.1}
\]

The same fixing bounds hold for the adjoints. In particular,
\(r=\varepsilon^{1/3}\), for \(0<\varepsilon<1\), gives
a four-unitary linear combination with coefficient absolute sum
two and errors \(O(\varepsilon^{1/3})\).

For a proof, write \(P(z)=\sum k_j^*zk_j\) and define
\(\mathcal E_P(z)=\operatorname{Re}\tau(z^*(z-Pz))\).
Bistochasticity and direct expansion give

\[
 2\mathcal E_P(z)=\sum_j\|[z,k_j]\|_2^2,
 \qquad \|Pz-z\|_2^2\leq2\mathcal E_P(z).
 \tag{14.2}
\]

Put \(h=\operatorname{Re}a=P(\operatorname{Re}x)\) and
\(k=\operatorname{Im}a=P(\operatorname{Im}x)\). Their
energies are at most \(\varepsilon\). On \([-1,1]\), the
unit-circle-valued function

\[
 f_r(t)=(1-r)t+i\sqrt{1-(1-r)^2t^2}
\]

has Lipschitz constant at most \(r^{-1/2}\), since
\[
 |f_r'(t)|^2=\frac{(1-r)^2}{1-(1-r)^2t^2}\leq\frac1r.
\]
Diagonalizing
\(h\) bounds each Hilbert--Schmidt commutator of \(f_r(h)\)
by \(r^{-1/2}\) times that of \(h\); the same holds for
\(k\). Equations (14.2) give the fixing bounds for
\(u_1=f_r(h)\), \(u_2=f_r(k)\). Their displayed linear
combination equals \((1-r)a\) exactly, proving (14.1).

However, closing almost-fixed unitaries under all products is
not a valid extraction step, even for heat with a fixed exact gap.
On \(M_2\), let \(X,Z\) be the usual Pauli matrices and let
\(\mathcal D\) be diagonal. Set, for \(n\geq2\),

\[
 t_n=\sin\frac{\pi}{2n},\quad
 P_n=(1-t_n)E_{\mathcal D}+t_n I
     =\exp\bigl(-(-\log t_n)(I-E_{\mathcal D})\bigr),
 \quad w_n=\exp\frac{i\pi X}{2n}.
 \tag{14.3}
\]

Here \(I-E_{\mathcal D}=(I-\operatorname{Ad}Z)/2\) has gap
one. Direct calculation gives

\[
 \delta_n=\|P_n^2-P_n\|_{\infty\to2}=t_n(1-t_n),
 \quad P_n(Z)=Z,
 \quad \|P_n(w_n)-w_n\|_2=\delta_n.
\]

But \(w_n^n=iX\) has fixing defect \(1-t_n\to1\).
The group generated by \(Z,w_n\) is finite, since
\(Zw_nZ=w_n^{-1}\) and \(w_n^{4n}=I\), and its generated
matrix algebra is all of \(M_2\). Expectation onto that algebra
is the identity map, at distance \(1-t_n\) from \(P_n\).
The correct expectation \(E_{\mathcal D}\) is only \(t_n\)
away. Thus (14.1) does not justify passing to the compact group
generated by its almost-fixed unitaries. It leaves open a
construction of a different nearby algebra or compact group.

### 14.1. A correctly selected compact group does suffice

There is a dimension-independent repair statement for a compact
subgroup already selected with the required uniform bounds. Let
\(P:M_d\to M_d\) be self-adjoint, bistochastic and UCP, put
\(\varepsilon=\|P^2-P\|_{\infty\to2}\), and let
\(G\subset U(d)\) be a compact subgroup. Set \(A=G''\), and
suppose

\[
 \sup_{g\in G}\|P(g)-g\|_2\leq\eta,\qquad
 \|(I-E_A)P\|_{\infty\to2}\leq\theta.
 \tag{14.4}
\]

Then

\[
 \boxed{\|P-E_A\|_{\infty\to2}
              \leq\theta+3\sqrt{\eta^2+\varepsilon}.}
 \tag{14.5}
\]

In particular, no assertion that the convex hull of \(G\) equals
the operator unit ball of \(A\) is needed.

Choose an adjoint-paired Kraus family for \(P\): replacing a
family \((a_j)\) by \((a_j/\sqrt2,a_j^*/\sqrt2)_j\) preserves
the channel because \(P=P^*\). Let

\[
 b_j=E_{A'}(a_j),\qquad
 \sigma=\sum_j\|a_j-b_j\|_2^2.
\]

Haar averaging over \(G\) is the trace-preserving expectation
onto \(A'\). The usual commutator identity for this averaging,
together with (14.2), gives

\[
 \sigma=\frac12\sum_j\int_G\|[g,a_j]\|_2^2\,dg
        =\int_G\mathcal E_P(g)\,dg.
 \tag{14.6}
\]

For a unitary \(g\), self-adjointness of \(P\) gives

\[
 \mathcal E_P(g)
 =\|(I-P)g\|_2^2+
        \operatorname{Re}\langle(P-P^2)g,g\rangle
 \leq\eta^2+\varepsilon.
\]

Thus \(\sigma\leq\eta^2+\varepsilon\).

The projected family \((b_j)\) is still adjoint-paired, so

\[
 D:=\sum_jb_j^*b_j=\sum_jb_jb_j^*\leq I.
\]

The inequality follows from Schwarz for \(E_{A'}\) and the
corresponding Kraus sum for \(P\). Put
\(c=(I-D)^{1/2}\in A'\), and define

\[
 R(x)=\sum_j b_j^*xb_j+cxc.
\]

This is a self-adjoint bistochastic UCP map, all of whose Kraus
operators lie in \(A'\). Consequently \(R|_A=\mathrm{id}_A\).
Orthogonality of \(E_{A'}\) in \(L^2\) also yields
\(\tau(c^2)=\sigma\).

Kraus Cauchy--Schwarz, using
\(\sum a_j^*a_j=I\) and \(\sum b_j^*b_j\leq I\), gives
for every contraction \(x\)

\[
 \left\|\sum_j a_j^*xa_j-\sum_jb_j^*xb_j\right\|_2
       \leq2\sqrt{\sigma},\qquad
 \|cxc\|_2\leq\sqrt{\sigma}.
\]

Hence \(\|P-R\|_{\infty\to2}\leq3\sqrt{\sigma}\), with
no dependence on the size of the Kraus family. Since \(R\) is
self-adjoint and fixes \(A\), it satisfies \(E_AR=E_A\).
The decomposition

\[
 P-E_A=(I-E_A)P+E_A(P-R)
\]

proves (14.5).

For example, if each of the four unitaries used in (14.1) is
within \(\zeta\) in \(L^2\) of \(G\), uniformly over
\(\|x\|\leq1\), then \(\theta\leq r+2\zeta\).
Together with uniform fixing on the whole of \(G\), this would
give expectation rounding. Section 14's finite-group example
shows why fixing bounds on proposed generators alone do not
supply that whole-group hypothesis.

## 15. Genuine Kazhdan heat can have maximal frame trace-norm defect

The trace-norm strengthening of section 12's frame estimate fails
even for heat maps of exact representations with a fixed Kazhdan
gap. There are finite-dimensional exact representations of
\(\Gamma=\mathrm{SL}_3(\mathbb Z)\) whose normalized traces
converge to the canonical trace, and times \(t_n\to\infty\)
such that

\[
 \|P_{n,t_n}-E_{\pi_n(\Gamma)'}\|_{2\to2}\longrightarrow0,
 \qquad
 \|R_{P_{n,t_n}^2}-R_{P_{n,t_n}}\|_1\longrightarrow2.
 \tag{15.1}
\]

All fixed valid group-algebra SOS identities have zero residual in
these models. Thus the trace-frame defect can be asymptotically
maximal while the heat maps actually round to exact expectations.
Here \(\|\cdot\|_1\) is the ordinary trace norm of operators on
the Hilbert space \(L^2(M_d,\tau_d)\), as in section 12.

First consider an infinite group \(G\) with finite symmetric
generating list \(S\), whose regular Laplacian

\[
 \mathcal L=I-|S|^{-1}\sum_{s\in S}\lambda(s)
      \quad\hbox{on }\ell^2(G)
\]

satisfies \(\mathcal L\geq\kappa I\) for some \(\kappa>0\).
This holds for the infinite property-T groups and Kazhdan lists
under consideration. Write \(\mu_t\) for the continuous-time
random-walk law with convolution operator \(e^{-t\mathcal L}\).
Then

\[
 \|\mu_{2j}-\mu_j\|_{\ell^1(G)}\longrightarrow2
        \qquad(j\longrightarrow\infty).
 \tag{15.2}
\]

Here is a direct proof of the required positive-speed statement.
Sample the walk at integer times. Its independent increments have
law \(\mu_1\) and finite first word moment: the number of generator
steps in one unit of time is Poisson with mean one.
[Kingman's subadditive ergodic theorem](https://academic.oup.com/jrsssb/article/30/3/499/7026968),
applied to word length, gives \(|X_j|/j\to v\) almost surely,
for a deterministic \(v\geq0\). Choose \(D>1\) with
\(|B_R(G)|\leq D^{R+1}\). The regular gap gives
\(\mu_j(g)\leq\|e^{-j\mathcal L}\|_{2\to2}\leq e^{-\kappa j}\),
so, for any \(a>0\) with \(a\log D<\kappa\),

\[
 \Pr(|X_j|\leq aj)
       \leq D^{aj+1}e^{-\kappa j}.
\]

This is summable. Borel--Cantelli implies \(v\geq a>0\).
The balls \(\{g:|g|\leq(3/2)vj\}\) consequently have
\(\mu_j\)-mass tending to one and \(\mu_{2j}\)-mass tending
to zero. This proves (15.2).

We next transfer this separation to canonical matrix models,
keeping the same finite-dimensional comparison space for both
times. Let \(V_{s,n}\) be inverse-paired unitary matrices with
full word coherence and canonical traces for \(G\). Thus equal
fixed group words have asymptotically equal matrices in normalized
\(2\)-norm, and the matrices of distinct fixed group elements
have asymptotically orthogonal normalized traces. Put

\[
 T_n(x)=|S|^{-1}\sum_{s\in S}V_{s,n}^*xV_{s,n},\qquad
 P_{n,t}=e^{-t(I-T_n)}.
\]

For an inverse-paired list this is the same heat map as with the
opposite convention for adjoint conjugation. Its Kraus frame is
the trace-norm convergent positive sum

\[
 R_{P_{n,t}}
   =e^{-t}\sum_{k\geq0}\frac{t^k}{k!}|S|^{-k}
       \sum_{w\in S^k}|V_n(w)\rangle\langle V_n(w)|.
 \tag{15.3}
\]

Every vector in this sum has normalized \(2\)-norm one; hence
\(R_{P_{n,t}}\geq0\) and \(\operatorname{Tr}(R_{P_{n,t}})=1\).

For a fixed cutoff \(K\), put \(F_K=B_K(G)\) and choose a word
\(w_g\) of length at most \(K\) for each \(g\in F_K\). Let
\(u_{g,n}=V_n(w_g)\), and define

\[
 \begin{split}
 \alpha_{n,K}
    &=\max_{|w|\leq K}\|V_n(w)-u_{\bar w,n}\|_{2,d_n},\\
 \beta_{n,K}
    &=\left\|\bigl[\tau_{d_n}(u_{g,n}^*u_{h,n})\bigr]_{g,h\in F_K}
                    -I\right\|_{\mathrm{op}}.
 \end{split}
 \tag{15.4}
\]

Here \(\bar w\) denotes the element represented by \(w\).
Both errors tend to zero for each fixed \(K\). If \(\beta_{n,K}<1/2\),
the map \(C:e_g\mapsto u_{g,n}\) has positive invertible Gram
matrix \(G_0=C^*C\), and
\(J_{n,K}=CG_0^{-1/2}\) is an isometry from \(\ell^2(F_K)\)
into \(L^2(M_{d_n},\tau_{d_n})\). Moreover

\[
 \max_{g\in F_K}\|u_{g,n}-J_{n,K}e_g\|_2
       \leq\|G_0^{1/2}-I\|_{\mathrm{op}}\leq\beta_{n,K}.
\]

Let \(q_t(K)=\Pr(\operatorname{Pois}(t)>K)\), and let
\(\nu_{t,K}(g)\) be the total Poisson-word weight of words of
length at most \(K\) representing \(g\). Thus
\(\nu_{t,K}\leq\mu_t\) and
\(\|\mu_t-\nu_{t,K}\|_{\ell^1}=q_t(K)\).
For unit vectors, the trace-norm distance between their rank-one
frames is at most twice their Hilbert-space distance. Truncating
(15.3), replacing equal group words by their representatives, and
then applying the common isometry gives

\[
 \left\|R_{P_{n,t}}
       -J_{n,K}\operatorname{diag}(\nu_{t,K})J_{n,K}^*\right\|_1
       \leq q_t(K)+2\alpha_{n,K}+2\beta_{n,K}.
 \tag{15.5}
\]

The same \(J_{n,K}\) works for \(t\) and \(2t\). Since
\(P_{n,t}^2=P_{n,2t}\) exactly, (15.5) yields the useful
cutoff inequality

\[
 \begin{split}
 \|R_{P_{n,t}^2}-R_{P_{n,t}}\|_1
 \geq{}&\|\mu_{2t}-\mu_t\|_{\ell^1}
       -2\bigl(q_t(K)+q_{2t}(K)\bigr)\\
       &-4\alpha_{n,K}-4\beta_{n,K}.
 \end{split}
 \tag{15.6}
\]

Choose integer stages \(t=j\geq3\), then a finite \(K_j\) with
\(q_j(K_j),q_{2j}(K_j)\leq1/j\). Only after fixing this stage
choose a matrix index threshold beyond which
\(\alpha_{n,K_j},\beta_{n,K_j}\leq1/j\). Taking increasing
thresholds and setting \(t_n=j\) between successive thresholds
gives \(t_n\to\infty\). Equations (15.2) and (15.6), together
with the universal upper bound two, imply

\[
 \|R_{P_{n,t_n}^2}-R_{P_{n,t_n}}\|_1\longrightarrow2.
 \tag{15.7}
\]

This diagonal can simultaneously impose
\(\varepsilon_n\leq j^{-3}\) at stage \(j\), for any fixed
row-residual sequence \(\varepsilon_n\to0\). In particular
\(t_n\varepsilon_n\to0\), so the times are admissible for the
[native fixed-SOS heat estimates](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md).
This uses finite word and Gram convergence at each prescribed
stage; it does not assume a modulus for growing-rank rounding.

For an unconditional example, take \(\Gamma=\mathrm{SL}_3(\mathbb Z)\)
and let \(\pi_p\) be reduction modulo a prime \(p\), followed
by the left regular representation of \(\mathrm{SL}_3(\mathbb F_p)\).
These are exact representations. A fixed nonidentity integer
matrix remains nonidentity modulo every sufficiently large prime,
so their normalized traces converge to the canonical group trace.
Thus word coherence is exact and the Gram matrices in (15.4) are
eventually exactly identity for each fixed cutoff. The fixed
property-T gap on their adjoint representations gives, uniformly
in \(p\),

\[
 \|P_{p,t}-E_{\pi_p(\Gamma)'}\|_{2\to2}\leq e^{-\kappa t},
 \qquad
 \|P_{p,t}^2-P_{p,t}\|_{\infty\to2}\leq e^{-\kappa t}.
 \tag{15.8}
\]

Every fixed valid SOS identity evaluates exactly. Applying the
slow diagonal above proves (15.1).

Conditionally, if canonical matrix microstates for the actual
\(H\) exist, restrict them to its infinite property-T subgroup
\(L\). The same argument gives admissibly slow native heat times
for which (15.7) holds, while the fixed-SOS estimates give
\(\|P_{n,t_n}^2-P_{n,t_n}\|_{\infty\to2}\to0\).
Therefore canonicality, a fixed adjoint-generator list, and the
fixed Kazhdan SOS residual do not imply small trace-norm defect
of the Kraus frames. The unconditional example also shows that
small trace-frame defect is not necessary for expectation
rounding. No failure of expectation rounding for \(H\), or
decision of its hyperlinearity, follows from this norm obstruction.

## 16. Metric approximate closure does not select a compact subgroup in the same dimension

There is no dimension-independent function \(f(\delta)\to0\)
with the following property: every compact, inverse-closed
\(K\subset U(d)\) containing \(I\) and satisfying
\[
 \sup_{u,v\in K}\operatorname{dist}_{2,d}(uv,K)\leq\delta
\]
lies within Hausdorff \(L^2\)-distance \(f(\delta)\) of a compact
subgroup of \(U(d)\). This fails even for finite \(K\), and it
still fails after closing \(K\) under multiplication by all scalar
unitaries. Here Hausdorff distance uses normalized
Hilbert--Schmidt distance in the given matrix dimension.

### 16.1. A finite-set counterexample with a fixed separation bound

Let \(q\geq128\) be a prime power, put \(n=q-1\), and take
\(G_q=PGL_2(\mathbb F_q)\). Its permutation action on the
\(q+1\) projective points is doubly transitive: an invertible
linear map can send any ordered pair of distinct lines to any
other such pair. The permutation representation therefore has
a two-dimensional commutant and splits as the trivial
representation plus an irreducible representation
\(\rho:G_q\to U(q)\). Every nonidentity projective transformation
fixes at most two projective points, so its deleted permutation
character satisfies
\[
 \operatorname{Tr}(\rho(g))\in\{-1,0,1\}\qquad(g\ne e).
 \tag{16.1}
\]

Choose an isometry \(J:\mathbb C^n\to\mathbb C^q\).
Let \(V_g\) be a unitary polar completion of \(J^*\rho(g)J\).
Choose \(V_e=I\) and \(V_{g^{-1}}=V_g^*\). For involutions,
a self-adjoint sign completion makes these requirements
compatible. The compression has all but at most one singular
value equal to one. If the remaining singular value is \(s\),
the squared Frobenius error of the lifted polar completion is
\((1-s^2)+(1-s)^2=2(1-s)\). Thus
\[
 \|\rho(g)J-JV_g\|_F\leq\sqrt2
 \quad\hbox{for every }g\in G_q.
 \tag{16.2}
\]

Set \(K_q=\{V_g:g\in G_q\}\). Telescoping (16.2) gives
\[
 \|V_gV_h-V_{gh}\|_{2,n}
       \leq\delta_q:=\frac{3\sqrt2}{\sqrt n}\longrightarrow0.
 \tag{16.3}
\]
The set is inverse-closed and contains \(I\), so this is the
strongest one-translate metric approximate-subgroup condition;
in particular its product set has Hausdorff distance at most
\(\delta_q\) from \(K_q\).

The labels are uniformly separated. For \(g\ne h\), (16.1)
gives \(\|\rho(g)-\rho(h)\|_F^2\geq2q-2\).
Removing the one-dimensional complement of \(J\) reduces that
squared norm by at most four. Hence
\[
 \|V_g-V_h\|_{2,n}
 \geq\frac{\sqrt{2q-6}-2\sqrt2}{\sqrt n}>1.
 \tag{16.4}
\]
For \(q\geq128\), also \(\delta_q<0.38\).

Suppose a compact subgroup \(C\subset U(n)\) had Hausdorff
distance less than \(1/10\) from \(K_q\). Each \(c\in C\)
has a unique label \(f(c)\in G_q\) with
\(\|c-V_{f(c)}\|_{2,n}<1/10\). The map \(f\) is continuous
and onto. It is a homomorphism: a discrepancy between the labels
of \(cd\) and \(f(c)f(d)\) would put two distinct elements of
\(K_q\) at distance less than \(3/10+\delta_q<1\), contrary
to (16.4).

Let \(N=\ker f\). Every \(k\in N\) is within \(1/10\) of
\(I\). Haar averaging \(p=\int_N k\,dk\) is the projection
onto the \(N\)-fixed subspace, and
\[
 \frac{\operatorname{rank}p}{n}
 =1-\frac12\int_N\|k-I\|_{2,n}^2\,dk
 \geq\frac{199}{200}.
 \tag{16.5}
\]
Normality of \(N\) makes \(p\) commute with \(C\). The action
on its range therefore factors through an exact representation
\(\sigma:G_q\to U(r)\), where
\(r=\operatorname{rank}p\leq n<q\).

For each \(g\), choose \(c_g\in C\) with \(f(c_g)=g\).
The isometry \(T=J|_{p\mathbb C^n}\) then satisfies
\[
 \|\rho(g)T-T\sigma(g)\|_F
       \leq\sqrt2+\frac1{10}\sqrt n.
 \tag{16.6}
\]
There is no nonzero intertwiner from \(\sigma\) to the
irreducible \(q\)-dimensional representation \(\rho\), because
\(r<q\). Averaging \(\rho(g)T\sigma(g)^*\) over the finite
group consequently gives zero. Equation (16.6) would imply
\[
 \sqrt{\frac{199}{200}}
 \leq\sqrt{\frac rn}
 \leq\sqrt{\frac2n}+\frac1{10},
\]
which is impossible for \(n\geq127\). Therefore
\[
 \boxed{\operatorname{dist}_{H,2,n}(K_q,C)\geq\frac1{10}
 \quad\hbox{for every compact subgroup }C\subset U(q-1).}
 \tag{16.7}
\]

### 16.2. Including all scalar phases does not repair selection

Let \(\widehat K_q=\mathbb T K_q\), where
\(\mathbb T=\{\lambda I:|\lambda|=1\}\).
These compact sets contain all scalar unitaries, remain
inverse-closed, and have the same product defect \(\delta_q\).
For \(q\geq65536\), their Hausdorff distance from every compact
subgroup of \(U(q-1)\) is at least \(1/100\).

Indeed, (16.4) also holds between distinct scalar cosets:
its proof uses \(|\operatorname{Tr}(\rho(g)^*\rho(h))|\leq1\)
and works for \(\rho(g)-\lambda\rho(h)\) uniformly in
\(|\lambda|=1\). If a compact subgroup \(C\) were within
\(\varepsilon=1/100\) of \(\widehat K_q\), unique projective
labels would again define a continuous surjective homomorphism
\(f:C\to G_q\). The multiplication estimate is now
\(3\varepsilon+\delta_q<1\).

Its kernel \(N\) lies within \(\varepsilon\) of the scalar
unitaries. Therefore, for every \(k\in N\),
\[
 |\tau_n(k)|\geq1-\varepsilon^2/2.
\]
Decompose the natural representation of \(N\) into distinct
irreducibles with dimensions \(d_j\) and multiplicities \(m_j\).
Haar character orthogonality gives
\[
 \frac1{n^2}\sum_jm_j^2
   =\int_N|\tau_n(k)|^2\,dk
   \geq\gamma:=(1-\varepsilon^2/2)^2.
 \tag{16.8}
\]
Since \(\sum_jm_j\leq n\), some multiplicity is at least
\(\gamma n>n/2\). Its irreducible has dimension one, and this
large multiplicity is unique. Conjugation by \(C\) preserves
multiplicities, so the associated isotypic projection \(p\)
commutes with \(C\). Write \(r=\operatorname{rank}p\geq\gamma n\).
On this subspace, \(N\) acts through a single scalar character.

For each \(g\), choose \(c_g\in C\) within \(\varepsilon\)
of \(V_g\), choosing \(c_e=I\). Restriction to \(p\) gives a
projective representation \(\sigma(g)\), with multiplier
\(\omega(g,h)\in\mathbb T\). For \(T=J|_{p\mathbb C^n}\),
(16.2) gives
\[
 \sup_g\frac{\|\rho(g)T-T\sigma(g)\|_F}{\sqrt r}
 \leq e_q:=
 \frac{\sqrt{2/n}+\varepsilon}{1-\varepsilon^2/2}
 <0.016.
 \tag{16.9}
\]
Comparing two products with \(\rho(gh)T\) shows
\(|\omega(g,h)-1|\leq3e_q\). Its principal argument
\(\vartheta(g,h)\) thus has absolute value at most \(6e_q\).
The multiplicative cocycle identity makes the additive
coboundary of \(\vartheta\) a multiple of \(2\pi\); its
absolute value is at most \(24e_q<2\pi\), so this coboundary
is zero.

Put \(b(g)=|G_q|^{-1}\sum_h\vartheta(g,h)\). Averaging the
real cocycle identity gives
\(\vartheta(g,h)=b(g)+b(h)-b(gh)\), with
\(|b(g)|\leq6e_q\). Consequently
\(\sigma'(g)=e^{-ib(g)}\sigma(g)\) is an exact representation
of \(G_q\) on dimension \(r<q\). Equation (16.9) gives it
uniform intertwining error at most \(7e_q<1\).
Finite-group averaging, as in (16.6), would force this error
to be at least one. This proves
\[
 \boxed{\operatorname{dist}_{H,2,n}(\widehat K_q,C)
       \geq\frac1{100}
 \quad\hbox{for every compact subgroup }C\subset U(q-1).}
 \tag{16.10}
\]

The obstruction is specific to keeping the same dimension.
In dimension \(q\), the exact compact groups \(\rho(G_q)\)
and \(\mathbb T\rho(G_q)\) approximate the corresponding
sets through the isometry \(J\), with uniform normalized
rectangular error at most \(\sqrt{2/(q-1)}\) by (16.2).
Thus this example does not refute a selection theorem allowing
a small change of dimension. Section 10 also leaves open
using such a flexible construction to obtain an algebra
expectation in the original dimension.

### 16.3. The CP fixing hypothesis adds information absent from the metric sets

The preceding sets are not counterexamples to channel rounding.
There is a quantitative reason why simply making a channel fix
them does not produce one. Let \(\Phi:M_n\to M_n\) be
bistochastic and UCP, without a self-adjointness assumption, and
suppose
\[
 \sup_{g\in G_q}\|\Phi(V_g)-V_g\|_{2,n}\leq\eta.
\]
Then
\[
 \boxed{\|\Phi-\mathrm{id}\|_{\infty\to2,n}
       \leq3\sqrt{\frac qn}
                  \left(\sqrt\eta+\frac2{\sqrt n}\right).}
 \tag{16.11}
\]
If \(\Phi\) is self-adjoint with idempotence defect
\(\varepsilon\), the \(\sqrt\eta\) term may be replaced by
\(\sqrt{\eta^2+\varepsilon}\).

To prove this, write \(\Phi(x)=\sum_i a_i^*xa_i\) and put
\[
 \kappa=\sum_i\|a_i-\tau_n(a_i)I\|_{2,n}^2
        =1-\sum_i|\tau_n(a_i)|^2.
\]
Lift \(a_i\) to \(A_i=Ja_iJ^*\in M_q\), and write
\(E_g=\rho(g)J-JV_g\), so \(\|E_g\|_F\leq\sqrt2\).
The exact commutator error is
\[
 [\rho(g),A_i]-J[V_g,a_i]J^*
       =E_g a_iJ^*-Ja_iE_{g^{-1}}^*.
 \tag{16.12}
\]
Its squared Frobenius norms, summed over \(i\), are at most
eight. This uses both identities
\(\sum_i a_i^*a_i=\sum_i a_ia_i^*=I\).

The Kraus energy identity gives
\(\frac12\sum_i\|[V_g,a_i]\|_{2,n}^2\leq\eta\).
Averaging (16.12) over the irreducible representation \(\rho\)
and using Minkowski's inequality therefore gives
\[
 \left(2\sum_i\operatorname{var}_q(A_i)\right)^{1/2}
       \leq\sqrt{\frac{2n\eta}{q}}+\sqrt{\frac8q}.
\]
The variance on the left is explicit:
\[
 \sum_i\operatorname{var}_q(A_i)
       =\left(\frac nq\right)^2\kappa+\frac n{q^2}.
\]
It follows that
\[
 \sqrt\kappa\leq
       \sqrt{\frac qn}\left(\sqrt\eta+\frac2{\sqrt n}\right).
\]
Project the Kraus operators to their scalar parts
\(\tau_n(a_i)I\). Kraus Cauchy--Schwarz bounds the change
of the channel by \(2\sqrt\kappa\). Completing this scalar
family by \(\sqrt\kappa I\) produces the identity channel
and costs at most \(\sqrt\kappa\). This proves (16.11).
For the self-adjoint refinement, use
\(\mathcal E_\Phi(V_g)\leq\eta^2+\varepsilon\) from section
14.1 instead of the bound by \(\eta\).

Thus a channel uniformly fixing these sets already approaches
the identity expectation as \(q\to\infty\) and \(\eta\to0\).
The example disproves selection from metric approximate closure,
even with scalar saturation; it does not disprove selection
using further CP bounded-image structure, and it does not decide
the rounding premise or hyperlinearity of \(H\).
