# Osgood microscopic extraction and a logarithmic spectral seed

Date: 2026-09-07. The nonhyperlinear-group target remains open. This
artifact proves a weaker sufficient seed hypothesis for its arithmetic
route. It does not construct that seed. All estimates below are analytic;
no matrix experiment, local execution, build, or formal verification is
claimed.

## 1. The precise general theorem

Fix a finite presentation `G=<S|R>` with longest relator length
`ell>=1`. Use inverse-compatible unitary tuples, and put

```text
delta(U)=max_(r in R)||U(r)-I||_(2,n),  U_s in U(n).
```

Let `psi:[0,b]->[0,infinity)` be continuous and nondecreasing, with
`psi(0)=0`, `psi(t)>0` for `t>0`, and

```text
integral_(0,b) dt/psi(t)=infinity.                     (OE1)
```

Suppose there is `delta_*>0`, with `delta_*^2<=b`, such that every
tuple of every dimension with `0<delta(U)<delta_*` admits at least
one of the following alternatives:

* An exact representation `rho:G->U(r)` with `1<=r<=n` and an
  isometry `J:C^r->C^n`, satisfying, for every generator,
  `||U_s J-J rho(s)||_HS^2 <= psi(delta(U)^2) r`.
* An exact representation `alpha:G->U(N)`, `N>=n`, in coordinates
  extending the input, satisfying
  `max_s||alpha(s)-(U_s direct_sum I_(N-n))||_(2,N)^2
  <=psi(delta(U)^2)` and `(N-n)/n<=psi(delta(U)^2)`.

Here the first alternative has no minimum rank fraction. Rank one is
permitted. The same function and threshold work for all tuples and
dimensions, including every residual tuple created below. The second
alternative may hold on any subset of inputs; it is not required
whenever the first alternative holds.

**Conclusion.** G is flexibly normalized-HS stable. Every sequence of
tuples with defining defects tending to zero admits exact corrections
with generator error and relative padding tending to zero. No property
(T), residual finiteness, or canonical-character assumption is needed
for this implication.

## 2. The finite dimension ledger

Start with a tuple on `C^d`, of defect `delta_0>0`. When the first
alternative is used, put the supplied isometry into coordinates,
remove its exact rank-`r_i` block, and polar-complete the remaining
compression. Choose inverse labels compatibly. Let `n_i` be the
current dimension, `x_i=n_i/d`, and let `xi_i^2` be a bound for its
retained-column squared error normalized by `r_i`; thus

```text
xi_i^2<=psi(delta(U^(i))^2),
A_i=(1/d)sum_(l<i) xi_l^2 r_l,
y_i=delta_0^2+3 ell^2 A_i.                            (OE2)
```

The established dimension ledger
`sequential-exact-corner-extraction-has-quadratic-error-ledger` gives,
for the block tuple `V_i` consisting of all extracted exact blocks
and the current residual,

```text
max_s||U_s^(0)-V_(i,s)||_(2,d)^2<=3A_i.              (OE3)
```

Its proof sums each complementary polar correction only once in
trace norm against the final later block unitary. Consequently (OE3)
has no factor for the number of cuts. This is essential when all
extracted ranks are microscopic.

Telescoping a relator of length at most ell in (OE3), and observing
that the extracted exact blocks have zero relator defect, gives

```text
sqrt(x_i) delta(U^(i)) <= delta_0+ell sqrt(3A_i),
delta(U^(i))^2 <= 2 y_i/x_i.                         (OE4)
```

Fix `0<theta<1`. Continue only while `x_i>theta`; stop if the
residual is exact or the full flexible alternative is used. A cut
strictly reduces the remaining integer dimension, so there are at
most d cuts. This is a finite algorithm in each dimension, although
the theorem assumes existence of its selected seeds rather than an
effective procedure for finding them.

For a cut at a current residual larger than `theta d`, (OE2)--(OE4)
and monotonicity of psi imply

```text
y_(i+1)<=y_i+F_theta(y_i) q_i,
q_i=r_i/d,
F_theta(y)=3 ell^2 psi(2y/theta).                    (OE5)
```

The sum of all q_i is at most one, including a last cut which first
crosses below `theta d` or removes the whole remaining space.

## 3. Osgood comparison with the threshold verified inductively

Choose `b_theta>0` with `2b_theta/theta<delta_*^2`. On
`(0,b_theta]`, F_theta is continuous, positive, and nondecreasing,
and substitution in (OE1) shows

```text
integral_(0,b_theta) dy/F_theta(y)=infinity.          (OE6)
```

For `a>0` small enough, define the increasing scalar flow `Y_a(t)`
for `0<=t<=1` by

```text
integral_(a,Y_a(t)) dy/F_theta(y)=t.                  (OE7)
```

The divergent integral ensures existence with `Y_a(1)<b_theta` for
all sufficiently small a. It also proves `Y_a(1)->0` as `a->0`:
for any fixed `c in (0,b_theta)`, the time to travel from a to c
diverges as a tends to zero.

This flow dominates every finite recurrence (OE5). Indeed, starting
at y, its growth over a time q is at least `q F_theta(y)`, because
F_theta is nondecreasing. The flow is increasing in its initial
value, by (OE7). Induction at the cumulative times
`t_i=sum_(l<i)q_l` therefore gives

```text
y_i<=Y_(delta_0^2)(t_i)<=Y_(delta_0^2)(1).            (OE8)
```

There is no assumption here that residual defects remain small.
That conclusion is part of the induction: before a seed is needed,
`x_i>theta` and (OE4), (OE8) give

```text
delta(U^(i))^2 <=2Y_(delta_0^2)(1)/theta
                 <2b_theta/theta<delta_*^2.
```

If this defect is zero, the residual is already exact; otherwise the
seed hypothesis applies. The resulting cut satisfies (OE5), which
proves the next step of (OE8). The final crossing cut is covered
because its q_i still lies in the total time interval of length one.

Thus, for each fixed theta, every stage and every terminal ledger
has `A_i->0` as `delta_0->0`, uniformly in d and the cut count.

## 4. Every stopping case gives a full correction

If a residual of size at most `theta d` is reached, replace it by
the trivial representation. The same established ledger gives a
same-dimensional exact correction with squared generator error

```text
3A_terminal+4theta.                                  (OE9)
```

If an exact residual is encountered earlier, its direct sum with the
already extracted exact blocks is an exact correction, with squared
generator error at most `3A_terminal`.

If the full flexible alternative is used earlier, put
`a_i=psi(delta(U^(i))^2)` and let its padding be p. Then
`p/d <= a_i n_i/d <= a_i`. Extend (OE3) by p identity coordinates
and combine it with this last residual correction. One final
squared triangle inequality gives the global estimate

```text
generator error squared <=6A_i
              +2a_i (n_i+p)/(d+p) <=6A_i+2a_i,
relative padding <=a_i.                              (OE10)
```

For fixed theta, (OE4), (OE8) and continuity of psi give `a_i->0`.
All stopping cases therefore have limiting squared generator error
at most `4theta` and limiting padding zero. Given any desired
positive tolerance, first choose theta small enough and then choose
delta_0 small enough. This proves correction of every sufficiently
small-defect tuple at that tolerance, and hence flexible stability.
There is no subsequence selection, density assumption, infinite
iteration at a fixed dimension, or unproved intermediate canonicality.

## 5. A logarithmic seed gives an explicit rate

In particular take, for sufficiently small t,

```text
psi(t)=K t log(e/t),             K>0.                 (OE11)
```

It is continuous and increasing on `(0,1)`, tends to zero, and
`integral_0 dt/[t log(e/t)]` diverges. Thus the retained-column
error may be `sqrt(K) delta sqrt(log(e/delta^2))`, which is larger
than a constant times delta, and the extraction still succeeds.

There is a sharper dimension clock than the fixed-theta comparison
needed for the general theorem. Put `C=6K ell^2`, and at a cut let
`u_i=r_i/n_i`. While `2y_i/x_i<min(1,delta_*^2)`, (OE4) gives

```text
y_(i+1)-y_i
 <=6K ell^2 y_i log(e x_i/(2y_i)) u_i
 <=C y_i log(e/y_i) u_i.                             (OE12)
```

For every cut that leaves `x_(i+1)>theta`,
`u_i<=-log(1-u_i)=log(x_i/x_(i+1))`. Their total clock is at most
`log(1/theta)`. A final crossing cut contributes at most one,
including `u_i=1`. If the algorithm stops by a different alternative,
there is no crossing contribution. In all cases

```text
sum_i u_i<=1+log(1/theta).                            (OE13)
```

The scalar flow `Y'=C Y log(e/Y)`, `Y(0)=delta_0^2`, is explicitly

```text
Y(t)=e exp(-L exp(-Ct)),     L=log(e/delta_0^2).       (OE14)
```

As long as Y is below one its right side is increasing in Y, so the
same finite Euler comparison used above applies. Choose

```text
theta=L^(-1/(2C)),
B_L=e exp(-exp(-C) sqrt(L)).                         (OE15)
```

For sufficiently small delta_0, theta lies in `(0,1)`. Equations
(OE13)--(OE15) give `y_i<=B_L` at every stage, including the terminal
cut. Moreover `2B_L/theta->0`; it is therefore below both the seed
threshold squared and one for all sufficiently large L. This
verifies the assumption preceding (OE12) inductively, with the same
argument as in Section 3.

The terminal flexible value satisfies
`a_i<=K(2B_L/theta)log(e theta/(2B_L))`, which tends to zero faster
than every negative power of L. Equations (OE9)--(OE10) now give

```text
generator error = O(L^(-1/(4C))),
relative padding = O(L^(-1/(2C))).                   (OE16)
```

All constants and the admissible initial defect depend only on the
presentation, K, and the seed threshold. The padding estimate is a
convenient common bound; the only case with nonzero padding has the
faster bound just displayed. No optimal exponent is asserted.

## 6. The resulting arithmetic spectral hypothesis

For `G=SL_5(Z)`, use the fixed symmetric elementary presentation,
Kazhdan set S, `h=|S|`, constant kappa, and universal finite quotient
`Q_(2n)` from
`moving-subgroup-schreier-correction-has-no-index-loss`. Let

```text
Delta_(Q_(2n),U)=(1/h)sum_s D_s*D_s,
D_s(T)=lambda_(Q_(2n))(s)T-TU_s.
```

It now suffices to prove constants `B>0`, `delta_*>0` such that,
for every dimension n and every inverse-compatible tuple with
`0<delta(U)<delta_*`,

```text
min Spec Delta_(Q_(2n),U)
 <=B delta(U)^2 log(e/delta(U)^2).                    (OE17)
```

This asks only for one spectral vector. It makes no normalized
spectral-count assumption. To verify sufficiency, set
`epsilon^2=B delta^2 log(e/delta^2)`, and shrink the threshold so
`a=2h epsilon^2/kappa^2<=1/2`. The full spectral space below that
cutoff is nonzero. The established `(MSC14)` gives an exact target
of dimension r, with

```text
r/n<=1/(1-a),
xi<=sqrt(h)epsilon+2sqrt(a/(1-a))
   <=sqrt(h)(1+4/kappa)epsilon.
```

When `r<=n`, its polar coisometry gives the first seed alternative
with squared error at most
`h(1+4/kappa)^2 B delta^2 log(e/delta^2)` normalized by r.
When `r>n`, its padded polar correction gives the second alternative,
with that squared generator bound and relative padding at most
`4h B delta^2 log(e/delta^2)/kappa^2`.
Thus (OE11) applies with

```text
K=max(h(1+4/kappa)^2 B,4h B/kappa^2).
```

The theorem proves flexible HS stability of SL5 conditional on
(OE17). The existing higher-rank co-dense HNN route then targets an
explicit nonhyperlinear group. Its arithmetic prerequisites remain
the existing Cairn dependencies; this artifact does not reprove them.

## 7. Scope, prior art, and the missing step

The Osgood integral criterion and scalar nonlinear comparison are
classical. Their use here is a self-contained extension of the
repository's September 5 dimension ledger from a linear seed rate
to the stated squared-modulus condition. Repository searches for
`Osgood` and logarithmic seed language on 2026-09-07 returned no
existing statement. A limited external search did not locate this
particular matrix-extraction theorem; global novelty is not certified.

The existing linear spectral estimate `(MSC19)` implies (OE17), since
`log(e/delta^2)>=1` at small defect. The reverse implication is not
proved. The successful class of moduli is enlarged, rather than
replaced by an equivalent assertion by definition.

Neither a merely qualitative seed modulus nor a power law
`psi(t)=K t^alpha`, `0<alpha<1`, satisfies (OE1). This proof therefore
does not repair that previously identified gap. Failure of the
integral condition is not asserted to imply instability: the scalar
comparison is a sufficient criterion, not a classification of groups.

The fresh target audit still finds the arithmetic existence claim
conditional in Dogon--Vigdorovich,
[Hyperlinearity, stability and asymptotic spectral gap of higher rank
lattices, version 2](https://arxiv.org/html/2506.20843v2), checked
2026-09-07. That paper does not supply (OE17). The new logarithmic
seed hypothesis likewise remains unproved here. In particular, no
nonhyperlinear discrete-group witness has been established in this
attack.
