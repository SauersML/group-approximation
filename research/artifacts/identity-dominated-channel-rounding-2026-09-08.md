# Tracial rounding from a fixed completely positive identity component

Date: 2026-09-08.

This proves expectation rounding under an additional, fixed identity
component. It does not establish the general quantum rounding premise
or the native Leavitt application. Traces on matrices are normalized;
traces of operators on Hilbert spaces are ordinary operator traces.

## 1. Statement

**Theorem.** Fix `0<lambda<=1`. Suppose bistochastic UCP maps
`P_n:M_(d_n)->M_(d_n)` satisfy

\[
 P_n-\lambda\,\mathrm{id}\text{ is CP},\qquad
 \zeta_n=\left(\int_{U(d_n)}
       \|P_n^2(u)-P_n(u)\|_2^2\,du\right)^{1/2}
       \longrightarrow0.
 \tag{1}
\]

There are unital subalgebras `A_n` in the original matrices with

\[
 \|P_n-E_{A_n}\|_{\infty\to2}\longrightarrow0.
 \tag{2}
\]

No self-adjointness hypothesis is required. The hypothesis is a
Haar average, whereas the conclusion is uniform over the full
operator unit ball. In particular, the theorem applies when the
stronger defect `||P_n^2-P_n||_(infinity->2)` tends to zero.
Equivalently, for each fixed positive `lambda` there is a
dimension-independent qualitative rounding modulus, even from the
Haar defect to uniform distance. We do not obtain an explicit rate. Values
`lambda>1` are excluded by evaluating the positive difference at one.

We prove this by contradiction in a tracial ultraproduct. A sequence
staying a fixed distance from every expectation cannot satisfy (1).

## 2. Ordered Kraus frames and product tails

Choose orthogonal Kraus vectors, padded with zeros and ordered by
their squared normalized Hilbert--Schmidt norms:

\[
 P_n(x)=\sum_i a_{i,n}^*x a_{i,n},\qquad
 \tau_n(a_{i,n}^*a_{j,n})=\beta_{i,n}\delta_{ij},
 \quad \beta_{1,n}\geq\beta_{2,n}\geq\cdots\geq0.
 \tag{3}
\]

Both marginal sums are one. Thus each `a_(i,n)` is a contraction,
`sum_i beta_(i,n)=1`, and `beta_(r+1,n)<=1/(r+1)`.
Write

\[
 R_n=\sum_i|a_{i,n}\rangle\langle a_{i,n}|
 \quad\text{on }L^2(M_{d_n},\tau_n).
\]

This positive frame has trace one. The usual Choi correspondence,
with its fixed vectorization isometry and normalized trace scaling,
identifies complete-positive order with frame order. In particular,

\[
 R_n\geq\lambda|1\rangle\langle1|.
 \tag{4}
\]

For any two finite Kraus families `a,b`, Haar integration gives

\[
 \|R_a-R_b\|_{\mathrm{HS}}^2
   =\int_{U(d)}\|P_a(u)-P_b(u)\|_2^2\,du.
 \tag{5}
\]

The cross term for individual vectors is
`integral <a*ua,b*ub> = |tau(a*b)|^2`. Consequently,

\[
 \left\|R_n-
       \sum_{i,j}|a_{i,n}a_{j,n}\rangle
                         \langle a_{i,n}a_{j,n}|\right\|_{\mathrm{op}}
 \leq\zeta_n.
 \tag{6}
\]

The following product-tail bound is crucial. For any `x` in normalized
`L^2`, Bessel's inequality gives

\[
 \begin{aligned}
 \sum_{i>r,j}|\tau_n(x^*a_{i,n}a_{j,n})|^2
 &\leq\beta_{r+1,n}\sum_j\|x a_{j,n}^*\|_2^2\\
 &=\beta_{r+1,n}\|x\|_2^2.
 \end{aligned}                                                   \tag{7}
\]

The equality uses `sum_j a_j* a_j=1`. Applying Bessel's inequality
on the other index and using `sum_i a_i a_i*=1` likewise bounds
the sum over `j>r` by the same quantity. Therefore deleting all
product pairs outside the first `r` indices changes their positive
frame by at most `2/(r+1)` in operator norm. Deleting the original
frame tail costs at most `1/(r+1)`. These are operator-norm bounds
on frames, not trace-norm bounds.

## 3. The atomic limit cannot lose trace mass

Let `M=prod_omega(M_(d_n),tau_n)`, with its faithful normalized trace
`tau`, and put `a_i=(a_(i,n))_omega`. The two monotone sums

\[
 h=\sum_i a_i^*a_i\leq1,\qquad
 h'=\sum_i a_i a_i^*\leq1
 \tag{8}
\]

exist strongly in `M`. Define the positive trace-class operator

\[
 R=\sum_i |a_i\rangle\langle a_i|
 \quad\text{on }L^2(M),\qquad
 \operatorname{Tr}R=\tau(h)=\tau(h')\leq1.
\]

Pass first to the ultralimit of each finite head in (6)--(7),
testing against bounded elements of `M`, then let `r` tend to
infinity. Such elements are dense in `L^2(M)`, and the operator
tail bounds are uniform. This gives

\[
 R=\sum_{i,j}|a_i a_j\rangle\langle a_i a_j|,
 \qquad R\geq\lambda|1\rangle\langle1|.
 \tag{9}
\]

Both positive series in (9) converge in trace norm: for the product
series, its trace is `tau(h h')<=1`, by normality and monotone sums.
Equality of the operators therefore gives

\[
 \tau(hh')=\tau(h)=\tau(h').
 \tag{10}
\]

Faithfulness implies `h(1-h')=(1-h')h=0` and the analogous
identities with `h,h'` exchanged. Thus `hh'=h=h'`, so
`h=h'=p` is a projection. Both Kraus marginal identities imply
`a_i=p a_i p` for every `i`. The vector `1-p` is consequently
orthogonal to the frame support. Testing the second inequality
in (9) against it gives `lambda tau(1-p)^2<=0`. Hence

\[
 h=h'=1,\qquad\operatorname{Tr}R=1.
 \tag{11}
\]

In particular, no Kraus trace mass escaped to the vanishing frame
eigenvalues. For every fixed `r`,

\[
 \lim_\omega\sum_{i>r}\|a_{i,n}\|_2^2
       =1-\sum_{i\leq r}\|a_i\|_2^2
       \longrightarrow0\quad(r\longrightarrow\infty).
 \tag{12}
\]

## 4. Compactness makes the limiting Kraus algebra finite

Let `B=W*(a_i:i>=1)` in `M`. Denote left multiplication by `L_a`.
The first identity in (9) is

\[
 \sum_i L_{a_i}R L_{a_i}^*=R.
 \tag{13}
\]

Both sums `sum L_(a_i)*L_(a_i)` and `sum L_(a_i)L_(a_i)*`
are one by (11). Expanding Hilbert--Schmidt commutators, with
nonnegative sums and trace-class convergence, gives

\[
 \sum_i\|[L_{a_i},R]\|_{\mathrm{HS}}^2
 =2\operatorname{Tr}(R^2)
   -2\operatorname{Tr}\left(R\sum_iL_{a_i}R L_{a_i}^*\right)=0.
 \tag{14}
\]

Thus `R` commutes with left multiplication by `B`. Using the other
product index in (9) gives the same result for right multiplication.
Adjoints cause no problem: an operator commuting with the self-adjoint
`R` has its adjoint commuting with `R` as well. This is why
self-adjointness of the original channels is unnecessary.

The support of `R` is initially contained in `L^2(B)`, since its
frame vectors belong to `B`. Inequality (9) puts the identity in
that support. Invariance under left multiplication then puts `B`,
and by closure `L^2(B)`, in the support. Therefore

\[
 \operatorname{supp}R=L^2(B).
 \tag{15}
\]

On the standard Hilbert space `L^2(B)`, an operator commuting with
both left and right multiplication belongs to the represented
center of `B`. Every nonzero spectral projection of the compact
positive `R` has finite Hilbert-space rank and is a central projection
of `B`. These projections exhaust its support. Splitting their
finite-dimensional central corners further shows

\[
 B=\prod_{j\in J}M_{b_j},\qquad
 \tau|_B=\sum_j t_j\operatorname{tr}_{b_j},
 \quad t_j>0,\quad\sum_jt_j=1,
 \tag{16}
\]

where `J` is at most countable. The frame is a positive scalar
`w_j` on each `L^2(M_(b_j))`.

For clarity, its scalar is forced, not an arbitrary spectral
parameter. An orthonormal matrix-unit basis for that block is
`sqrt(b_j/t_j) e_(kl)`. The identity `R=sum |a_i><a_i|`, restricted
to this block, and the marginal `sum a_i* a_i=1` imply

\[
 1=w_j\sum_{k,l}
       (\sqrt{b_j/t_j}\,e_{kl})^*
       (\sqrt{b_j/t_j}\,e_{kl})
   =w_j\frac{b_j^2}{t_j}\,1.
\]

Thus `w_j=t_j/b_j^2`. To use (9) without any inverse-domain issue,
take a finite set `F` of blocks and the vector
`x_F=sum_(j in F) w_j^(-1) z_j`, where `z_j` is its identity
projection. Then

\[
 \langle x_F,Rx_F\rangle
   =\sum_{j\in F}\frac{t_j}{w_j}
   =\sum_{j\in F}b_j^2,
 \qquad
 \langle1,x_F\rangle=\sum_{j\in F}b_j^2.
\]

The domination inequality gives

\[
 \lambda\left(\sum_{j\in F}b_j^2\right)^2
       \leq\sum_{j\in F}b_j^2.
\]

Consequently

\[
 \boxed{\dim_{\mathbb C} B=\sum_j b_j^2\leq1/\lambda.}
 \tag{17}
\]

The algebra `B` is finite-dimensional. This conclusion was obtained
without assuming an a priori bound on the coordinate Kraus ranks.

## 5. Lift the finite source and compare the full channels

Choose a fixed system of matrix units for `B`. Lift them to exact
matrix units in corners `p_n M_(d_n) p_n`, giving homomorphisms

\[
 \pi_n:B\longrightarrow p_nM_{d_n}p_n,
 \quad\tau_n(1-p_n)\longrightarrow_\omega0,
 \quad\|\pi_n(a_i)-a_{i,n}\|_2\longrightarrow_\omega0
 \tag{18}
\]

for every fixed `i`. Here is the finite lifting construction: lift
the diagonal projections orthogonally, trim the equivalent projections
within each simple block to their smallest common rank, and complete
polar factors of the off-diagonal lifts to partial isometries between
these equal-rank supports. Products of those partial isometries give
exact matrix units. The finitely many trace discrepancies tend to
zero, so the dimension removed is `o_omega(d_n)`. Divisibility does
not require an exact unital embedding into the entire original matrix.

Frame equality in (9) is equality of the quadratic Kraus coefficient
matrices in any fixed linear basis of `B`. Such equality remains
true in every representation of `B`. The marginal identities (11)
also transport. It follows that

\[
 Q_n(x)=\sum_i\pi_n(a_i)^*x\pi_n(a_i)
                 +(1-p_n)x(1-p_n)
 \tag{19}
\]

is exactly unital, trace-preserving, completely positive and
idempotent. The displayed series can equivalently be expressed using
a finite Kraus family, by factoring its finite quadratic coefficient
matrix. A bistochastic UCP idempotent is the trace-preserving
expectation onto its fixed algebra: Schwarz and faithfulness make
each fixed element belong to the multiplicative domain, so the fixed
space is a unital algebra. Thus `Q_n=E_(A_n)`.

Here is the uniform comparison, including the tails. A CP map `T`
with `T(1)<=1` satisfies `T(x)*T(x)<=T(x*x)` on contractions,
so `||T||_(infinity->2)<=sqrt(tau(T(1)))`. Apply this to both
Kraus tails after a fixed index `r`. For the heads, contractivity
of the individual Kraus operators gives

\[
 \begin{aligned}
 \|P_n-Q_n\|_{\infty\to2}
 &\leq 2\sum_{i\leq r}\|a_{i,n}-\pi_n(a_i)\|_2\\
 &\quad+\sqrt{1-\sum_{i\leq r}\tau_n(a_{i,n}^*a_{i,n})}\\
 &\quad+\sqrt{\tau_n\!\left(\pi_n
                  (1-\sum_{i\leq r}a_i^*a_i)\right)}
       +\sqrt{\tau_n(1-p_n)}.
 \end{aligned}                                                     \tag{20}
\]

The head and last terms vanish along `omega`. The two remaining
terms tend to the square root of
`1-sum_(i<=r) tau(a_i* a_i)`, which tends to zero by (11).
First take the ultralimit and then `r` to infinity. This contradicts
the assumed fixed separation and proves the theorem and its uniform
modulus formulation.

## 6. Scope for canonical long-time heat

The hypothesis is complete-positive domination, not an inequality
between eigenvalues of the superoperator on `L^2`. It is stronger
than having an arbitrarily small identity term in a Kraus formula.

In fact, for canonical long-time heat maps of an infinite group,
the largest allowable identity coefficient tends to zero. Here is
the needed purity calculation. Let `S` be a fixed finite symmetric
generating list, let `V_(n,s)` be inverse-paired canonical matrix
microstates, and put

\[
 A_n=1-|S|^{-1}\sum_s\operatorname{Ad}V_{n,s},\qquad
 P_n=e^{-t_n A_n},\qquad t_n\longrightarrow\infty.
\]

Canonicality means that the normalized trace of every fixed word
tends to zero for a nonidentity group element and to one for the
identity. Haar isotropy and (5) give

\[
 \chi_n^2:=\|R_{P_n}\|_{\mathrm{HS}}^2
   =d_n^{-2}\operatorname{Tr}(P_n^2).
\]

For every fixed `T>0`, positivity of `A_n` and `t_n>=T` eventually
bound this by `d_n^(-2) Tr(exp(-2T A_n))`. Expand the latter by its
Poisson word series. The trace of `Ad(V_w)` divided by `d_n^2` is
`|tau_n(V_w)|^2`. Fixed-word canonicality and the uniform Poisson
tail bound therefore make its limit the return probability
`mu_(2T)(e)` for continuous-time simple random walk on the group.
That probability tends to zero as `T` tends to infinity: on the
regular representation, the heat converges strongly to invariant
vectors, and an infinite group has no nonzero constant vector in
`ell^2(G)`. Thus `chi_n->0`.

If
`R_(P_n)>=lambda_n |1><1|`, testing against the unit vector one
gives

\[
 \lambda_n\leq\langle1,R_{P_n}1\rangle
      \leq\|R_{P_n}\|_{\mathrm{op}}
      \leq\chi_n\longrightarrow0.
 \tag{21}
\]

This excludes every fixed positive coefficient, including coefficients
arising from a better Kraus representation than the literal zero-step
Poisson term. No control of the rounding modulus as `lambda` tends to
zero has been established. Thus (1)--(20) settle a further class of
quantum channels while leaving the native rounding premise and the
headline nonhyperlinearity objective open.
