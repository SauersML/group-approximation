# Finite receiver tests can miss a canonical Kazhdan commutant

2026-09-08. Written finite-dimensional and representation arguments.
No computation or build. This is a counterexample to replacing the
uniform scalar-heat test in component selection by prescribed test
averages. It is not a counterexample to conditional-expectation
rounding and makes no assertion about hyperlinearity of the Leavitt
unit group.

All traces and Hilbert--Schmidt norms are normalized. Write
\(E_{\rm sc}(x)=\tau(x)I\).

## 1. A fixed projection can be invisible to a prescribed test distribution

Let \(D\) be even and let \(\mu\) be any Borel probability
measure on the operator unit ball of \(M_D\). There is a
self-adjoint unitary \(h\), with \(\tau(h)=0\), such that
\(A=\mathbb C I+\mathbb C h\) satisfies

\[
\int\|(E_A-E_{\rm sc})(x)\|_2^2\,d\mu(x)
 \leq\frac1{D^2-1},\qquad
\|E_A-E_{\rm sc}\|_{\infty\to2}=1.                 \tag{1}
\]

The two minimal projections of \(A\) each have trace \(1/2\).
Thus the missed invariant is a projection of fixed positive trace.

To prove this, put \(h_0=\operatorname{diag}(I_{D/2},-I_{D/2})\)
and Haar-rotate \(h=W h_0W^*\). Conjugation on traceless complex
matrices is irreducible, so its averaged rank-one covariance is

\[
\int_{U(D)}|Wh_0W^*\rangle\langle Wh_0W^*|\,dW
 =\frac{I-E_{\rm sc}}{D^2-1}.                      \tag{2}
\]

For completeness, invariance under diagonal unitaries and permutation
matrices shows that a conjugation-invariant complex subspace containing
a nonzero off-diagonal matrix contains every off-diagonal matrix;
two-coordinate rotations then supply the traceless diagonals.
A nonscalar diagonal matrix produces an off-diagonal matrix by such
a rotation. This proves irreducibility. The scalar in (2) follows
by taking Hilbert-space trace: each rank-one covariance has trace
\(\|h_0\|_2^2=1\).

Consequently, for every \(x\in M_D\),

\[
\int_{U(D)}|\tau(Wh_0W^*x)|^2\,dW
 =\frac{\|x\|_2^2-|\tau(x)|^2}{D^2-1}.            \tag{3}
\]

Since \((E_A-E_{\rm sc})(x)=\tau(hx)h\), integrate (3)
against \(\mu\) and choose a rotation no worse than the mean.
This proves the first part of (1). The unitary \(h\) is a witness
for the second part, and orthogonal projection gives the upper bound.

The order of quantifiers is essential: the test distribution is
chosen before the rotation. A test allowed to inspect \(A\) and
then put mass one on \(h\) detects the missing direction exactly.

There is also a uniform test on an entire prescribed algebra. For
any unital subalgebra \(F\subset M_D\), (2) gives

\[
\int_{U(D)}\|E_F(Wh_0W^*)\|_2^2\,dW
 =\frac{\dim_{\mathbb C}F-1}{D^2-1}.
\]

Since \(|\tau(hx)|\leq\|E_F(h)\|_2\) for contractions
\(x\in F\), some rotation satisfies

\[
\|(E_A-E_{\rm sc})|_F\|_{\infty\to2}^2
 \leq\frac{\dim_{\mathbb C}F-1}{D^2-1}.            \tag{4}
\]

Thus a prescribed noncommutative receiver algebra of dimension
\(o(D^2)\) can be tested uniformly on its whole operator ball
without detecting the global error one. For several prescribed
algebras, summing their covariance bounds gives the same conclusion
when the sum of their dimensions is \(o(D^2)\).

## 2. Realization by exact canonical representations of one ICC Kazhdan group

These failures occur for genuine fixed-group adjoint heat maps.
Let \(\Gamma=SL_3(\mathbb Z)\) and \(G=\Gamma\times\Gamma\).
For each prime \(p\), let \(\pi_p\) be the deleted permutation
representation of the action of \(SL_3(\mathbb F_p)\) on its
projective plane, composed with reduction from \(\Gamma\).
The [existing irreducible-model proof, section 6.1](leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md)
gives the following elementary facts.

The projective action is doubly transitive: map two independent
representatives of distinct lines to another such pair and adjust
the third basis vector to make determinant one. The permutation
commutant therefore has dimension two. After its single trivial
summand, the remaining representation \(\pi_p\) is irreducible,
of dimension \(d_p=p^2+p\). Reduction from \(\Gamma\) is
surjective because elementary matrices generate the finite field
group.

For each fixed \(g\ne1\) in \(\Gamma\), reduction of \(g\)
is nonscalar for all sufficiently large primes. A nonscalar matrix
in dimension three fixes at most \(p+2\) projective points:
its fixed lines are its eigenspaces' one-dimensional subspaces,
and the largest possible eigenspace has dimension two. Hence

\[
|\tau(\pi_p(g))|\leq\frac1p
\quad\text{for all sufficiently large }p.           \tag{5}
\]

Take distinct primes \(p_n,q_n\to\infty\), and define exact
representations of \(G\) by

\[
\begin{aligned}
\sigma_{n,1}(g_1,g_2)&=\pi_{p_n}(g_1)\otimes\pi_{q_n}(g_2),\\
\sigma_{n,2}(g_1,g_2)&=\pi_{q_n}(g_1)\otimes\pi_{p_n}(g_2),\\
\rho_n^0&=\sigma_{n,1}\oplus\sigma_{n,2},
\qquad D_n=2d_{p_n}d_{q_n}.
\end{aligned}                                                     \tag{6}
\]

The two summands are irreducible and inequivalent. Their first-factor
irreducible types have different dimensions \(d_{p_n}\ne d_{q_n}\),
so restriction to the first \(\Gamma\) distinguishes them.
They have equal total dimension. Schur's lemma gives

\[
\rho_n^0(G)'=\mathbb C I+\mathbb C h_0,
\qquad h_0=\operatorname{diag}(I_{D_n/2},-I_{D_n/2}).             \tag{7}
\]

Each summand, and therefore their direct sum, has canonical limiting
trace on \(G\), by (5). All relations hold exactly.

The group \(\Gamma\) has property (T); this standard input is
also recorded in [Ioana's introduction](https://ems.press/content/serial-article-files/51186).
Fix a finite symmetric generating set \(S_0\) of \(\Gamma\)
and its positive adjoint-Laplacian gap. For
\(S=(S_0\times\{1\})\cup(\{1\}\times S_0)\), the two
factor Laplacians commute. Their common-invariant projection is
the product of their invariant projections. Thus \(G\) has a
uniform gap \(\kappa>0\) for this fixed \(S\).

Both groups are ICC. In \(SL_3(\mathbb Z)\), a finite-index
centralizer contains a nonzero power of every elementary
transvection. Commuting with these powers forces a matrix to be
scalar, and the only integral scalar of determinant one in odd
dimension three is the identity. The product of two ICC groups
is ICC as well.

Choose any unitaries \(W_n\), put
\(\rho_n=\operatorname{Ad}(W_n)\rho_n^0\), and let

\[
\mathcal L_n=I-|S|^{-1}\sum_{s\in S}\operatorname{Ad}(\rho_n(s)),
\qquad P_{n,t}=e^{-t\mathcal L_n},
\qquad A_n=\rho_n(G)'.
\]

These are self-adjoint bistochastic UCP heat maps, positive on
\(L^2\), and the exact representation gap gives

\[
\|P_{n,t}-E_{A_n}\|_{2\to2}\leq e^{-\kappa t},
\qquad
\|P_{n,t}^2-P_{n,t}\|_{\infty\to2}\leq e^{-\kappa t}.          \tag{8}
\]

There is no relation-defect restriction on heat times, since all
fixed SOS equality rows have defect zero. Take any \(t_n\to\infty\).

## 3. Prescribed averages and fixed group words both miss the center

Given arbitrary prescribed test measures \(\mu_n\) on
\((M_{D_n})_1\), choose \(W_n\) using (1). The two terms in

\[
P_{n,t_n}-E_{\rm sc}
 =(E_{A_n}-E_{\rm sc})+(P_{n,t_n}-E_{A_n})
\]

have orthogonal ranges. Equations (1) and (8) therefore give

\[
\boxed{\int\|(P_{n,t_n}-E_{\rm sc})(x)\|_2^2\,d\mu_n(x)
 \leq\frac1{D_n^2-1}+e^{-2\kappa t_n}\longrightarrow0,}
                                                                    \tag{9}
\]

while, exactly for every \(n,t_n\),

\[
\boxed{\|P_{n,t_n}-E_{\rm sc}\|_{\infty\to2}=1.}              \tag{10}
\]

The witness is \(h_n=W_nh_0W_n^*\), which is trace zero and is
fixed by the heat. Contractivity on the orthogonal complement of
the scalars gives the matching upper bound.

If a list contains \(k_n\) prescribed contractions, choose the
uniform test measure. The same proof bounds the squared error at
every point of the list by
\(k_n/(D_n^2-1)+e^{-2\kappa t_n}\). In particular all tests
can pass when \(k_n=o(D_n^2)\). Alternatively, (4) gives
uniform convergence on the entire ball of any prescribed algebra
\(F_n\) of dimension \(o(D_n^2)\), while (10) still holds.

The models also pass all fixed group-word tests, which need not be
chosen independently of the representation. For a fixed \(g\in G\),
write \(a_{n,i}=\tau(\sigma_{n,i}(g))\). The scalar-versus-commutant
expectation error on \(\rho_n(g)\) is
\(|a_{n,1}-a_{n,2}|/2\), which tends to zero by canonicality of
both summands. Equation (8) supplies the additional vanishing heat
error. This persists after every chosen conjugation \(W_n\).

Nevertheless the full external commutant in the tracial matrix
ultraproduct is precisely

\[
\rho(G)'\cap\prod_\omega M_{D_n}
 =\prod_\omega A_n\cong\mathbb C\oplus\mathbb C.              \tag{11}
\]

Indeed the same uniform Kazhdan gap sends every bounded sequence
asymptotically commuting with the fixed generators to its coordinate
commutant at vanishing \(L^2\) distance. The equal-weight
two-dimensional coordinate algebras have ultraproduct \(\mathbb C^2\).

Thus testing scalar-heat convergence only by prescribed averages,
fixed group words, or a prescribed receiver algebra of small relative
vector-space dimension does not certify a scalar full commutant,
even for an ICC Kazhdan group with exact canonical representations.
In particular it cannot replace the uniform component cost in the
current selection proof without an additional argument.

The heat maps here round uniformly to their correct expectations
\(E_{A_n}\). Either irreducible summand in (6) can itself be
selected to obtain a canonical model with scalar commutant. Hence
this example neither obstructs the existence of a better selection
nor applies automatically to tests chosen adaptively from the full
heat map. It isolates the failure of the proposed test-based
certificate and does not refute the general rounding premise.
