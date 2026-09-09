# Tracial channel rounding from a bounded-Kraus minorant

2026-09-08. Written matrix and ultraproduct proof. No computation,
build, job, or new Lean verification is asserted.

This extends the fixed identity-component argument to a bistochastic
minorant of bounded Kraus rank. The finite minorant supplies both
full support and a dimension bound. We prove the required atomic-frame
steps here, without a dependency on an unproved rounding statement.

All matrix traces are normalized. A Hilbert-space operator trace or
Hilbert--Schmidt norm of a Kraus frame is unnormalized.

## 1. Statement

Fix `0<lambda<=1` and `r>=1`. Suppose `P_n,Q_n` are bistochastic
UCP maps on `M_(d_n)` with

```text
P_n-lambda Q_n CP,       Kraus_rank(Q_n)<=r,
zeta_n=(integral_(U(d_n)) ||P_n^2(u)-P_n(u)||_2^2 du)^(1/2)->0.
                                                        (1)
```

Then there are unital subalgebras `A_n subset M_(d_n)` such that

```text
||P_n-E_(A_n)||_(infinity->2)->0.                       (2)
```

Neither map need be self-adjoint. The conclusion is uniform on the
whole operator unit ball in the original dimension. By contradiction,
the sequential statement is equivalent to a dimension-independent
qualitative modulus for each fixed pair `(lambda,r)`. No rate is
asserted. The stronger mixed-norm idempotence defect bounds `zeta_n`.

Assume, for a contradiction, that a sequence satisfying (1) stays
at a fixed positive distance from every expectation. Pass to its
tracial ultraproduct `M=prod_omega(M_(d_n),tau_n)`.

## 2. Ordered frames and their atomic limit

Choose Kraus families, padded by zeros, as follows:

```text
P_n(x)=sum_i a_(i,n)* x a_(i,n),
tau_n(a_(i,n)* a_(j,n))=beta_(i,n) delta_ij,
beta_(1,n)>=beta_(2,n)>=...>=0,

Q_n(x)=sum_(j=1)^r b_(j,n)* x b_(j,n).                 (3)
```

All these Kraus operators are contractions. Each family's two
marginal sums are the identity. In particular
`sum_i beta_(i,n)=1` and `beta_(k+1,n)<=1/(k+1)`.

For any Kraus family `c`, put `R_c=sum_i |c_i><c_i|` on normalized
`L^2`. The Choi correspondence identifies CP order with order of
these positive frames. Thus, writing `R_n=R_(a_n)`,

```text
R_n>=lambda R_(b_n).                                  (4)
```

Haar integration gives the exact identity

```text
||R_c-R_e||_HS^2
 =integral_(U(d)) ||sum_i c_i* u c_i-sum_j e_j* u e_j||_2^2 du.
                                                        (5)
```

Indeed, the cross term for two Kraus vectors is
`integral <c*uc,e*ue> du=|tau(c*e)|^2`. Apply (5) to `P_n`
and `P_n^2`; their Kraus families are respectively `(a_i)` and
`(a_i a_j)`, with the order of the two indices immaterial. Hence

```text
||R_n-sum_(i,j)|a_(i,n)a_(j,n)><a_(i,n)a_(j,n)||_op<=zeta_n.
                                                        (6)
```

The frame after index `k` has operator norm at most `1/(k+1)`.
For products, Bessel's inequality gives, for every `x in L^2`,

```text
sum_(i>k,j) |tau_n(x* a_(i,n)a_(j,n))|^2
 <=beta_(k+1,n) sum_j ||x a_(j,n)*||_2^2
 =beta_(k+1,n)||x||_2^2.                               (7)
```

The equality uses `sum_j a_j* a_j=1`. The analogous bound with
`j>k` uses `sum_i a_i a_i*=1`. Thus deleting all product pairs
outside the first `k` indices costs at most `2/(k+1)` in frame
operator norm. These are not claims of small trace-norm tails.

Put `a_i=(a_(i,n))_omega`, `b_j=(b_(j,n))_omega`, and define

```text
h=sum_i a_i* a_i<=1,       h'=sum_i a_i a_i*<=1,
R=sum_i |a_i><a_i|,        R_b=sum_(j=1)^r |b_j><b_j|.   (8)
```

The marginal sums exist strongly. The positive frame `R` is trace
class, with trace `tau(h)=tau(h')<=1`. The finite minorant family
retains its exact marginal identities:

```text
sum_(j=1)^r b_j* b_j=sum_(j=1)^r b_j b_j*=1.            (9)
```

Taking the ultralimit on finite heads of (4)--(7), and then letting
`k` tend to infinity, gives

```text
R=sum_(i,j) |a_i a_j><a_i a_j|,
R>=lambda R_b.                                        (10)
```

For precision, test first against bounded elements of `M`. Their
finite inner products converge, and the uniform operator-tail bounds
control what was discarded. Density then extends the identities
to all of `L^2(M)`.

## 3. The minorant prevents loss of Kraus trace mass

The positive product series in (10) has trace `tau(hh')<=1`, by
normality of the trace and monotone sums. Thus equality in (10)
implies

```text
tau(hh')=tau(h)=tau(h').                               (11)
```

For positive contractions `h,h'`, faithfulness applied to
`h^(1/2)(1-h')h^(1/2)` gives `h(1-h')=(1-h')h=0`.
Interchanging them gives the other pair of identities. Hence
`h=h'=p` is a projection. The marginals in (8) imply
`a_i=p a_i p` for every `i`, so the support of the frame `R` is
contained in `L^2(pMp)`.

Domination in (10) puts every `b_j` in the support of `R`: the
kernel of `R` is contained in the kernel of `R_b`, whose orthogonal
complement is the span of the finitely many `b_j`. Therefore
`b_j=p b_j p`. Equation (9) now forces `p=1`. We have proved

```text
h=h'=1,       Tr(R)=1.                                (12)
```

In particular,

```text
lim_omega sum_(i>k) ||a_(i,n)||_2^2
 =1-sum_(i<=k)||a_i||_2^2 ->0 as k->infinity.           (13)
```

This is the trace-tail control that was unavailable before using
the finite minorant.

## 4. The supported compact frame is central on its Kraus algebra

Let `B=W*(a_i:i>=1) subset M`, and write `L_a` for left
multiplication. The first identity in (10) reads

```text
sum_i L_(a_i) R L_(a_i)*=R.
```

Both operator marginal sums are one by (12). Expanding
Hilbert--Schmidt commutators and taking positive sums gives

```text
sum_i ||[L_(a_i),R]||_HS^2
 =2Tr(R^2)-2Tr(R sum_i L_(a_i) R L_(a_i)*)=0.          (14)
```

Thus `R` commutes with left multiplication by `B`. The other
product index gives the same conclusion for right multiplication.
Commutation with adjoints follows because `R` is self-adjoint;
self-adjointness of the coordinate channels was never needed.

Let `S` be the support subspace of `R`. Its frame vectors lie in
`B`, so `S subset L^2(B)`. By (10), every `b_j` belongs to `S`.
Since `b_j` is bounded and belongs to `L^2(B)`, it belongs to `B`:
the trace-preserving expectation onto `B` fixes it in `L^2` and
hence fixes it as a bounded element of `M`.
Left invariance of `S` therefore gives

```text
b_j* b_j in S,       sum_(j=1)^r b_j* b_j=1 in S.
```

Multiplying the identity on the left by `B` and taking closure
proves `S=L^2(B)`.

On this standard Hilbert space, the intersection of the left and
right commutants is the represented center of `B`. The positive
compact operator `R` consequently acts as a central operator.
Its positive eigenspace projections have finite Hilbert-space rank
and exhaust `L^2(B)`. Each such central corner of `B` is finite
dimensional. Splitting them into simple blocks yields

```text
B=product_(ell in J) M_(m_ell),
tau|_B=sum_ell t_ell tr_(m_ell),       t_ell>0,
sum_ell t_ell=1,                                      (15)
```

with at most countably many blocks. On a block of degree `m_ell`,
the frame is multiplication by a positive scalar `w_ell`.

The marginal `sum_i a_i* a_i=1` determines this scalar. An
orthonormal matrix-unit basis on that block is
`sqrt(m_ell/t_ell)e_kl`. Comparing its quadratic coefficients in
the frame with those of the Kraus vectors gives

```text
1=w_ell sum_(k,l) (sqrt(m_ell/t_ell)e_kl)*
                         (sqrt(m_ell/t_ell)e_kl)
 =w_ell (m_ell^2/t_ell)1,
w_ell=t_ell/m_ell^2.                                 (16)
```

## 5. Finite-rank domination bounds the entire source dimension

Let `F` be any finite set of blocks in (15), let `z_F` be their
central identity projection, and compress both frames to `L^2(z_F B)`.
Write the compressions as `R_F` and `R_(b,F)`. The first is strictly
positive on this finite-dimensional space. By (10),

```text
0<=T_F:=R_F^(-1/2) R_(b,F) R_F^(-1/2)<=lambda^(-1)I,
rank(T_F)<=r.                                        (17)
```

Its trace is explicit. Equation (9), centrality of the block
projections `z_ell` in `B`, and (16) give

```text
Tr(T_F)
 =sum_(j=1)^r ||R_F^(-1/2) z_F b_j||_2^2
 =sum_(ell in F) w_ell^(-1) sum_(j=1)^r ||z_ell b_j||_2^2
 =sum_(ell in F) t_ell/w_ell
 =sum_(ell in F) m_ell^2.                             (18)
```

But (17) bounds this trace by `r/lambda`. Since `F` was arbitrary,

```text
dim_C(B)=sum_ell m_ell^2<=r/lambda.                    (19)
```

There are finitely many blocks. In particular the source dimension
is at most `floor(r/lambda)`, without a bound on the Kraus ranks
of `P_n` themselves.

## 6. Lift the finite source and recover uniform map convergence

Lift a fixed system of matrix units for the finite algebra `B` to
exact matrix units in corners `p_n M_(d_n) p_n`, obtaining
homomorphisms `pi_n:B->p_n M_(d_n) p_n` with

```text
tau_n(1-p_n)->_omega0,
||pi_n(a_i)-a_(i,n)||_2->_omega0 for every fixed i.     (20)
```

One direct lifting construction is to lift the diagonal projections
orthogonally, trim the equivalent projections in each simple block
to their smallest common rank, and use polar completions of the
off-diagonal lifts between equal-rank supports. Their products give
exact matrix units. The finitely many rank discrepancies are `o(d_n)`,
so the discarded relative dimension tends to zero. This does not
require divisibility for an exactly unital lift onto all of `M_(d_n)`.

The product-frame identity (10) is equality of the quadratic Kraus
coefficient matrices in any fixed linear basis of `B`. It and the
two marginals (12) transport under every representation of `B`.
Consequently

```text
E_n(x)=sum_i pi_n(a_i)* x pi_n(a_i)+(1-p_n)x(1-p_n)     (21)
```

is exactly bistochastic, UCP, and idempotent. The series may be
replaced by a finite Kraus family by factoring its finite coefficient
matrix. A bistochastic UCP idempotent is a trace-preserving
conditional expectation: Schwarz and trace faithfulness put each
fixed element in its multiplicative domain. Thus `E_n=E_(A_n)`
for a unital algebra in the original `M_(d_n)`.

For a subunital CP map `T`, Schwarz gives
`||T||_(infinity->2)<=sqrt(tau(T(1)))`. Apply this to both Kraus
tails after index `k`, and telescope the finite heads. Then

```text
||P_n-E_n||_(infinity->2)
 <=2sum_(i<=k)||a_(i,n)-pi_n(a_i)||_2
   +sqrt(1-sum_(i<=k)||a_(i,n)||_2^2)
   +sqrt(tau_n(pi_n(1-sum_(i<=k) a_i* a_i)))
   +sqrt(tau_n(1-p_n)).                              (22)
```

First take the ultralimit. The finite-head and complement terms
vanish; the two tails tend to the square root of
`1-sum_(i<=k)||a_i||_2^2`. Let `k` tend to infinity and use (12).
This contradicts the assumed fixed separation, proving (2) and the
uniform modulus formulation.

## 7. Canonical long-time heat excludes all fixed finite minorants

There is an exact finite-dimensional obstruction. If `P,Q` are
bistochastic UCP, `P-lambda Q` is CP, and `rank(R_Q)<=r`, let `e`
be the support projection of `R_Q` in the Hilbert space `L^2(M_d)`.
Since `Tr(R_Q)=1`, frame order and Hilbert--Schmidt Cauchy--Schwarz
give

```text
lambda<=Tr(e R_P)
       <=sqrt(rank(e))||R_P||_HS
       <=sqrt(r)||R_P||_HS.                           (23)
```

For completeness, consider canonical matrix microstates of an
infinite group with a fixed finite symmetric generating list `S`.
Let `V_(n,s)` be inverse-paired generator lifts and

```text
L_n=I-|S|^(-1)sum_(s in S) Ad(V_(n,s)),
P_n=exp(-t_n L_n),       t_n->infinity.
```

The `L_n` are positive on normalized `L^2`. Haar isotropy and
(5) give

```text
chi_n^2:=||R_(P_n)||_HS^2=d_n^(-2)Tr(P_n^2).
```

For each fixed `T>0`, this is eventually bounded by
`d_n^(-2)Tr(exp(-2T L_n))`. Its Poisson word expansion has terms
`|tau_n(V_w)|^2`, which converge to one or zero according as the
fixed group word is the identity or not. The uniform Poisson tail
bound permits passing to the limit, giving the continuous-time
random-walk return probability `mu_(2T)(1)`.

As `T->infinity` this probability tends to zero: regular heat
converges strongly to its invariant subspace, and an infinite group
has no nonzero constant vector in `ell^2(G)`. Thus `chi_n->0`.
Equation (23) excludes any fixed `lambda>0` and fixed `r`, even
when the minorants are chosen anew for every matrix and are not
visible in the literal Poisson expansion.

The theorem includes the identity-component case by `Q_n=id`,
and bounded-Kraus-rank rounding by `Q_n=P_n`, `lambda=1`.
Those conclusions are qualitative and require no self-adjointness.
An application to native long-time heat would need control as the
coefficient vanishes or the Kraus rank grows. General expectation
rounding and nonhyperlinearity remain unresolved here.
