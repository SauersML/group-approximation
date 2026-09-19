# Real filling escape is already a FALSE certificate

Date: 2026-08-11

## 1. Outcome

Let

`P=<S | R>`                                                   `(RFE1)`

be finitely presented and let `1!=w in Rad_sof(P)`.  In every finite
presentation cover the lifted `w`-loop has an integral filling.  Write
`q_(w,x)` for its unique minimum-norm **real** filling in the orthogonal
complement of the real two-cycle space.

The first result of this note is the direct estimate

`Lambda_(w,X) >= ||q_(w,x)||`                                  `(RFE2)`

for every finite exact `P`-set `X` and every vertex `x`.  Here
`Lambda_(w,X)` is the exact marked paired-discriminant ratio of
`FALSE_MARKED_DISCRIMINANT_DIVERGENCE_CRITERION.md`.  Consequently,

`sup_(X,x)||q_(w,x)||=infinity`                                 `(RFE3)`

already proves that a hyperlinear nonsofic group exists.

There is also a precise compactness alternative.  Let `K_n` be a nested
sequence of finite-index subgroups of `P`, let `K=intersection_n K_n`, and
assume `w in [K_n,K_n]` for every `n`.  If the real filling norms in the
finite covers stay bounded along a subsequence, then the lifted `w`-loop in
the infinite `K`-cover has an `ell^2` cellular filling.  Thus, if that loop
has no `ell^2` filling, its real finite-cover filling norms tend to infinity
and `(RFE2)` proves FALSE.

For an integral loop which is nonzero in `K_ab`, the minimum integral
filling norms always tend to infinity.  Hence exactly one of the following
two phenomena occurs along a residual tower:

1. the real coexact filling norms diverge, which proves FALSE;
2. a bounded real subsequence converges to an `ell^2` filling in the
   infinite cover, while the integral correction is forced out to infinity
   in the marked discriminant lattice.

This isolates the remaining obstruction sharply.  It is not ordinary
commutator filling area: only an `ell^2`-diffuse filling in the infinite
radical cover can prevent the real-filling route from completing the
counterexample.

**Update.**  `FALSE_NONAMENABLE_STABILIZER_FILLING_REDUCTION.md` proves
that this diffuse filling does exist for the explicit stable Laurent
double.  A nonamenable subgroup stabilizes the marked homology class and a
regular-representation divergence equation constructs the filling.  The
same argument localizes every finite-cover real filling, up to a uniform
additive constant, to one Kazhdan-subgroup orbit average.  The general
criteria below remain valid; the infinite-cover branch is now decided for
that example.

## 2. The infinitesimal marked-ratio bound

Let `Y_X` be the presentation complex over a finite exact `P`-set `X`.  As
in the discriminant notes, use the cellular bases and put

`A_X=d_X^1:C^1(Y_X,R)->C^2(Y_X,R)`,
`W_X=ran(A_X)`.                                             `(RFE4)`

For a vertex `x`, let `b_(w,x)` be the lifted word cycle.  Since `w` belongs
to the sofic radical, the finite-index radical theorem gives an integral
filling, and the canonical real filling is

`q_x=q_(w,x)=(A_X^dagger)^* b_(w,x) in W_X`,
`A_X^*q_x=b_(w,x)`.                                      `(RFE5)`

Let

`T_X:W_X->R^X`,
`(T_X y)_z=<b_(w,z),A_X^dagger y>=<q_(w,z),y>`.          `(RFE6)`

The exact marked ratio is

`Lambda_(w,X)`
` =sup_(y in W_X minus L_X)`
`   dist(T_Xy,Z^X)/dist(y,Z^(X times R))`,              `(RFE7)`

where `L_X=W_X intersect Z^(X times R)`.  The nonlinear discriminant
formula identifies the denominator in `(RFE7)` with the exact lower
envelope of the paired discriminant wells, but the following lower bound
already comes from the well at the origin.

**Theorem 1 (coexact filling lower bound).**  For every `x in X`,

`Lambda_(w,X)>=||T_X q_x||/||q_x||>=||q_x||`,           `(RFE8)`

with the evident convention when `q_x=0`.

**Proof.**  For all sufficiently small positive `t`, apart from a discrete
set which may be avoided, `tq_x` is not in `L_X`, zero is the closest
integer vector both to `tq_x` and to `tT_Xq_x`, and therefore

`dist(T_X(tq_x),Z^X)/dist(tq_x,Z^(X times R))`
` =||T_Xq_x||/||q_x||`.                                `(RFE9)`

The `x`-coordinate of `T_Xq_x` is

`(T_Xq_x)_x=<q_x,q_x>=||q_x||^2`.                     `(RFE10)`

Thus `||T_Xq_x||>=||q_x||^2`, which proves `(RFE8)`.  End proof.

**Corollary 2 (real filling escape proves FALSE).**  If a sequence of
finite exact `P`-sets contains vertices `x_n` such that

`||q_(w,x_n)||->infinity`,                             `(RFE11)`

then there is a hyperlinear nonsofic group.

**Proof.**  Theorem 1 makes the exact marked ratios unbounded.  Apply the
marked discriminant divergence theorem.  Its positive tensor amplification
turns any rate of divergence into a tracial matrix-ultraproduct
representation which retains `w`.  End proof.

This criterion is strictly infinitesimal.  It does not require selecting a
nonzero discriminant class or obtaining a macroscopic word phase at one
finite stage.

## 3. Compactness of bounded real fillings

Let `Y` be the finite presentation complex of `P` and let `Y_K` denote the
cover corresponding to a subgroup `K<=P`.  Give every cellular chain group
its standard Euclidean norm.  If

`K_1>=K_2>=...`, ` [P:K_n]<infinity`,
`K=intersection_n K_n`,                                  `(RFE12)`

then the pointed covers `Y_(K_n)` converge locally to `Y_K`: every fixed
combinatorial ball about the base vertex is eventually identical to the
corresponding ball in `Y_K`.  This follows directly because only finitely
many words of bounded length must be separated from `K`.

**Theorem 3 (`ell^2` compactness alternative).**  Suppose the lift of `w`
is closed in every cover in `(RFE12)` and there are real two-chains `z_n`
such that

`partial_2 z_n=b_(w,K_n)`,  `sup_n||z_n||_2<infinity`. `(RFE13)`

Then there is `z in ell^2(C_2(Y_K))` satisfying

`partial_2 z=b_(w,K)`.                                  `(RFE14)`

In particular, if `(RFE14)` has no solution, the minimum real filling norms
in the finite covers tend to infinity.

**Proof.**  Enumerate the two-cells of `Y_K`.  Local convergence identifies
each fixed finite initial set with cells of `Y_(K_n)` for all sufficiently
large `n`.  The coefficients of `z_n` on each such cell are bounded by the
common norm bound.  A diagonal subsequence therefore converges coefficient
by coefficient to a function `z` on the two-cells of `Y_K`.

For every finite set `F` of two-cells, Fatou's lemma gives

`sum_(c in F)|z(c)|^2<=liminf_n||z_n||_2^2`.            `(RFE15)`

Taking the supremum over finite `F` proves `z in ell^2` with the same norm
bound.  The cellular boundary equation at one edge involves only the
finitely many incident two-cells.  Local convergence and coefficientwise
convergence therefore pass `(RFE13)` to the limit at every edge, giving
`(RFE14)`.  The final assertion is the contrapositive, using minimum-norm
real fillings for `z_n`.  End proof.

Combining Theorem 3 with Corollary 2 gives the usable statement:

**Corollary 4 (infinite-cover criterion).**  Let `w in Rad_sof(P)` and let
`K_n` be as in `(RFE12)`.  If the lifted `w`-cycle is not in the range of

`partial_2:ell^2(C_2(Y_K))->ell^2(C_1(Y_K))`,          `(RFE16)`

then FALSE holds.

Notice that nonvanishing in ordinary homology is not enough for `(RFE16)`.
An ordinary nonboundary can be the boundary of a diffuse `ell^2` chain.
That distinction is exactly the analytic boundary left by this theorem.

## 4. Integral filling escape

For a finite cover in which the lifted loop is integrally null-homologous,
write

`Fill_Z,2(w;K_n)`
` =min{||z||_2:z in C_2(Y_(K_n),Z), partial_2z=b_w}`.  `(RFE17)`

**Theorem 5 (integral filling escape).**  Under `(RFE12)`, if

`w notin [K,K]`,                                      `(RFE18)`

then

`Fill_Z,2(w;K_n)->infinity`.                           `(RFE19)`

The same conclusion holds for every integral `ell^p` filling norm,
`1<=p<=infinity`, when the norm also records support size; in particular it
holds for `ell^1` and `ell^2`.

**Proof.**  Suppose integral `ell^2` fillings of norm at most `C` exist
along a subsequence.  Every nonzero integral coefficient has absolute value
at least one, so every filling has at most `C^2` cells in its support.

Join two support cells when their boundaries share an edge.  A support
component whose boundary does not meet the fixed loop `b_w` is an integral
two-cycle and may be deleted without affecting the filling or increasing
its norm.  Every remaining component meets `b_w` and contains at most
`C^2` cells.  Since the presentation has bounded relator length, all of its
cells lie in one fixed combinatorial neighborhood of `b_w`, independent of
`n`.

There are only finitely many integral chains of norm at most `C` in that
neighborhood.  Local convergence therefore supplies one chain which occurs
along a further subsequence and lifts to an integral chain in `Y_K` with
boundary `b_(w,K)`.  This makes the homology class of `w` vanish in
`H_1(Y_K,Z)=K_ab`, contrary to `(RFE18)`.  This proves `(RFE19)`.

For `ell^1` the support bound is immediate.  More generally, the same proof
works whenever bounded norm bounds both the nonzero coefficients and the
support.  End proof.

For the unmodified `ell^infinity` coefficient norm alone, the statement is
false as written because support may grow; this is why support size is
included in the last formulation.

## 5. Exact discriminant Pythagoras

Let `K_(2,n)=ker(partial_(2,n)) intersect C_2(Y_(K_n),Z)` be the integral
two-cycle lattice.  For any integral filling `z_n`, split

`z_n=q_n+u_n`,
`q_n perpendicular ker(partial_(2,n))`,
`u_n in ker(partial_(2,n))_R`.                         `(RFE20)`

The class

`c_n=u_n+K_(2,n) in K_(2,n)^#/K_(2,n)`                `(RFE21)`

is the canonical radical filling class.  Orthogonality and minimization in
the coset give the exact identity

`Fill_Z,2(w;K_n)^2=||q_n||^2+rho_(K_(2,n))(c_n)^2`.    `(RFE22)`

Indeed every other integral filling is `z_n+k`, with `k in K_(2,n)`, so
its orthogonal component is fixed at `q_n` while its cycle component ranges
over the coset `u_n+K_(2,n)`.

Combining Theorems 3 and 5 with `(RFE22)` gives the promised dichotomy.  If
`w notin [K,K]`, then either

`||q_n||->infinity`                                   `(RFE23)`

along a subsequence, which proves FALSE by Corollary 2, or a bounded
subsequence produces an `ell^2` filling in `Y_K` and necessarily

`rho_(K_(2,n))(c_n)->infinity`                        `(RFE24)`

along that subsequence.  The exact nonlinear repair formula shows where
this second alternative lives: all nonlinear integral repair is encoded by
paired discriminant wells.  But `(RFE24)` alone is not a FALSE certificate;
one still needs a small paired class on which the marked discriminant
character is nonzero.

## 6. Application to the explicit radical double

For the binary or stable integral polynomial/Laurent Kun--Thom pair, let

`D=G *_Gamma G`, `F=G *_N G`,
`R_0=ker(D->F)=Rad_sof(D)`.                             `(RFE25)`

The group `F` is finitely generated and residually finite.  Choose nested
finite-index normal subgroups

`F=L_0>L_1>...`, `intersection_n L_n=1`,               `(RFE26)`

and put `K_n=pi^(-1)(L_n)`.  Then `intersection_n K_n=R_0`.  For

`h in N minus Gamma`,
`w=i_2(h)i_1(h)^(-1)`,                                 `(RFE27)`

the Bass--Serre calculation gives

`[w]=delta_(hGamma)-delta_Gamma!=0 in (R_0)_ab`.       `(RFE28)`

The finite-index radical theorem gives `w in [K_n,K_n]` at every finite
stage, whereas `(RFE28)` gives `w notin [R_0,R_0]`.  Hence the integral
filling norms diverge by Theorem 5.

The zero-eigenvalue part of the `ell^2` alternative can be decided.  Let

`H_(2)=ker(partial_1) intersect ker(partial_2^*)`       `(RFE28a)`

be the harmonic realization of reduced `ell^2` homology in the `R_0`-cover.
It is a subrepresentation of a finite multiple of the left regular
representation of the deck group `F`, hence is tempered.

**Theorem 6 (the marked loop has zero harmonic component).**  The
orthogonal projection of `b_(w,R_0)` to `H_(2)` is zero.  Equivalently, its
spectral measure for `Delta_1=partial_2 partial_2^*` has no atom at zero.

**Proof.**  Algebraic homology and the Bass--Serre calculation give the
`ZF`-module

`H_1(Y_(R_0),Z)=(R_0)_ab`
` ~=A=ker(Z[F/Gamma]->Z[F/N])`.                       `(RFE28b)`

Projection of a finite cellular cycle to `H_(2)` kills ordinary cellular
boundaries, so it induces an `F`-equivariant additive map

`T:A->H_(2)`.                                         `(RFE28c)`

We recall why every such map into a tempered representation is zero.  For
`n in N` put

`e_n=delta_(nGamma)-delta_Gamma in A`.                 `(RFE28d)`

The identities `e_(mn)=e_m+m e_n` and `e_gamma=0` show that
`c(n)=T(e_n)` is a one-cocycle of the Kazhdan group `N`.  Hence

`c(n)=pi(n)xi-xi`                                     `(RFE28e)`

for some `xi`.  Since `c(gamma)=0`, the vector `xi` is `Gamma`-invariant.
But a tempered `F`-representation restricts to a representation weakly
contained in a multiple of `lambda_Gamma`; the infinite nonamenable group
`Gamma` has no invariant vector there.  Thus `xi=0`, so `T(e_n)=0` for all
`n`.  The `F`-translates of these differences generate `A`, hence `T=0`.

Apply this to `(RFE28c)`.  In particular the image of the class `(RFE28)`
is zero, which is precisely the harmonic projection of its cellular cycle.
For a cycle, the zero spectral projection of `Delta_1` is the harmonic
projection, proving the equivalent formulation.  End proof.

The exact remaining alternative is now:

* if the minimum real fillings in these mixed finite quotients are
  unbounded, the explicit finitely presented group `D` has a hyperlinear
  nonsofic image;
* otherwise the primitive parallel-edge loop `(RFE28)` admits an `ell^2`
  filling in the infinite `R_0`-cover, and all forced divergence is in the
  marked discriminant correction `(RFE24)`.

The nonamenable-stabilizer theorem cited in the update after Section 1
proves that the second infinite-cover alternative occurs.  This does not by
itself bound the finite-cover minimum real fillings: possible divergence is
localized to the rational invariant orbit averages described there.

The earlier `Q*Q`-only tower had a larger fixed kernel containing `w` in
its commutator subgroup, so one fixed integral filling bounded both terms
in `(RFE22)`.  The present residual tower is genuinely different: its
common kernel is the full free sofic radical and the marked word survives
in its abelianization.  Thus no fixed filling can exist.

## 7. Status

Theorems 1, 3, and 5 are rigorous.  Together they convert the unresolved
FALSE problem on the explicit double into one operator-range question in a
single infinite cover.  They do not yet decide whether the relevant
`ell^2` filling exists.  The next useful calculation is the spectral
measure at zero of the infinite-cover operator

`Delta_1=partial_2 partial_2^*`                         `(RFE29)`

at the marked parallel-edge cycle `b`.  In spectral-measure notation, an
`ell^2` filling exists exactly when `b` has no component in
`ker(partial_2^*)` and

`integral_((0,infinity)) lambda^(-1) d mu_b(lambda)<infinity`. `(RFE30)`

Theorem 6 proves the first condition for the explicit double.  The later
nonamenable-stabilizer filling theorem proves in addition that

`integral_((0,infinity)) lambda^(-1) d mu_b(lambda)`
`  <infinity`.                                               `(RFE31)`

Thus the infinite spectral-tail route is closed for this candidate.  At
finite levels, real filling escape can still occur through the invariant
orbit-average mode; all noninvariant Kazhdan modes have a uniform decoder.
The integral excess remains in the paired-discriminant branch.
