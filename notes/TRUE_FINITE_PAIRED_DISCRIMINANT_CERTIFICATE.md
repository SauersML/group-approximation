# Nonlinear integral repair has a finite exact quadratic certificate

Date: 2026-08-11

## Purpose

`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` identifies the optimal
circle-repair constant with the quotient of two periodic distance functions:
an ellipsoidal distance to the saturated range lattice, divided by the lower
envelope of the paired discriminant wells.  That formula is exact, but it
still contains a continuous supremum over a fundamental domain.

This note removes that last infinitary feature on every fixed chart.  Only
finitely many range sites and finitely many paired discriminant sites can be
active on a compact fundamental polytope.  Their common Voronoi refinement is
a finite rational polyhedral complex, and on each cell the squared repair
ratio is a quotient of two explicit rational quadratic polynomials.

Consequently:

* an asserted upper bound is equivalent to finitely many exact quadratic
  nonpositivity statements on rational polytopes;
* the optimal squared repair constant is a real algebraic number; and
* exact chart calculations do not require sampling phases or enumerating
  arbitrary integral carries.

This is an exact certification theorem for a fixed chart.  It does not by
itself bound the constants uniformly over the projective prime family.

## 1. Setup and the two finite site sets

Use the notation of the nonlinear discriminant formula.  Thus

`Lambda=Z^m subset R^m`,
`W=ran(A)`, `L=Lambda intersect W`,
`K=Lambda intersect W^perp`,                                      `(FPC1)`

and

`gamma:D_K=K^#/K -> D_L=L^#/L`                                  `(FPC2)`

is the canonical unimodular gluing.  Assume that `A` is an integral matrix
and that `0<dim(W)<m`.  Let

`H_A=(A^+)^* A^+`                                                 `(FPC3)`

be the positive-definite rational quadratic form on `W`.  For `ell in L`
and for `a in L^#` representing `gamma(c)`, define

`q_ell(y)=<H_A(y-ell),y-ell>`,                                    `(FPC4)`

`r_(c,a)(y)=||y-a||^2+rho_K(c)^2`.                               `(FPC5)`

The exact nonlinear formula says

`N(y):=d_(A,L)(y)^2=min_(ell in L) q_ell(y)`,                     `(FPC6)`

`D(y):=dist(y,Lambda)^2`
`     =min_(c in D_K) min_(a in gamma(c)) r_(c,a)(y)`,            `(FPC7)`

and

`C_circ(A)^2=sup_(y in W minus L) N(y)/D(y)`.                    `(FPC8)`

Choose a closed rational fundamental parallelepiped `P` for `L`.  Boundary
points may occur more than once under translation; this causes no problem
because both functions in `(FPC6)--(FPC7)` are `L`-periodic.

Define the active site sets

`S_N(P)={ell in L:there exists y in P with q_ell(y)=N(y)}`,       `(FPC9)`

`S_D(P)={(c,a):c in D_K, a in gamma(c),`
`                 there exists y in P with r_(c,a)(y)=D(y)}`.    `(FPC10)`

**Lemma 1 (finite activity).**  The sets `S_N(P)` and `S_D(P)` are finite.
Moreover the minima in `(FPC6)--(FPC7)` may be restricted to these sets for
every `y in P`.

**Proof.**  Fix `ell_0 in L`.  The function `q_(ell_0)` is bounded on the
compact set `P`, say by `M_N`.  If `ell` is active at `y`, then

`q_ell(y)<=q_(ell_0)(y)<=M_N`.                                   `(FPC11)`

Since `H_A` is positive definite on `W`, `(FPC11)` puts `ell` in a bounded
subset of the discrete lattice `L`.  Hence only finitely many numerator
sites are active.

For the denominator, the zero discriminant class and `ell_0` give the
competitor

`r_(0,ell_0)(y)=||y-ell_0||^2`,                                  `(FPC12)`

which is bounded on `P`, say by `M_D`.  If `(c,a)` is active at `y`, then

`||y-a||^2+rho_K(c)^2<=M_D`.                                    `(FPC13)`

There are already only finitely many classes `c in D_K`, and `(FPC13)` puts
`a` in a bounded subset of the discrete coset `gamma(c) subset L^#`.
Therefore `S_D(P)` is finite.  The last assertion is the definition of
activity.  End proof.

The proof is constructive.  Any explicit upper bounds for `(FPC11)` and
`(FPC13)` give finite lattice balls containing all active sites.  One may
discard a candidate after an exact Voronoi-feasibility test.

## 2. The paired Voronoi complex

For `ell in S_N(P)` and `(c,a) in S_D(P)`, put

`V_(ell,c,a)=P`
` intersect {y:q_ell(y)<=q_(ell')(y) for every ell' in S_N(P)}`
` intersect {y:r_(c,a)(y)<=r_(c',a')(y)`
`                    for every (c',a') in S_D(P)}.`               `(FPC14)`

**Lemma 2 (rational polyhedral refinement).**  Every nonempty
`V_(ell,c,a)` is a rational polytope, and these polytopes cover `P`.
On `V_(ell,c,a)`,

`N(y)=q_ell(y)`, `D(y)=r_(c,a)(y)`.                              `(FPC15)`

**Proof.**  The two numerator quadratics in a comparison have the same
quadratic part `H_A`, so

`q_ell-q_(ell')`                                                 `(FPC16)`

is affine linear.  Likewise every denominator branch in `(FPC5)` has
quadratic part equal to the Euclidean identity, so

`r_(c,a)-r_(c',a')`                                              `(FPC17)`

is affine linear.  All coefficients are rational: `A^+`, the dual lattices,
and the squared shortest-coset radii are rational.  Thus `(FPC14)` is an
intersection of finitely many rational half-spaces with `P`.  Lemma 1 and
the definitions of the cells prove the covering and `(FPC15)`.  End proof.

The walls in this complex have a precise meaning.  Numerator walls change
the closest exact integral carry.  Denominator walls change the closest
ambient integer vector, equivalently the active paired discriminant well.
No additional nonlinear discontinuity remains.

## 3. Exact finite certificate

Let `mathcal V(P)` be the finite collection of nonempty polytopes in
`(FPC14)`.

**Theorem 3 (finite paired-discriminant certificate).**

`C_circ(A)^2`
` =max_(V_(ell,c,a) in mathcal V(P))`
`    sup_(y in V_(ell,c,a) minus L) q_ell(y)/r_(c,a)(y).`         `(FPC18)`

Equivalently, for a real number `T>=0`,

`C_circ(A)^2<=T`                                                  `(FPC19)`

if and only if, for every cell `V_(ell,c,a) in mathcal V(P)`,

`q_ell(y)-T r_(c,a)(y)<=0 for every y in V_(ell,c,a).`            `(FPC20)`

The inequality in `(FPC20)` may include the points of `L`: at such a point
both sides of the underlying ratio vanish, and `(FPC20)` is still the
correct limiting condition.

**Proof.**  Periodicity restricts `(FPC8)` to `P`.  Lemma 2 covers `P` by
finitely many cells and identifies the two active quadratic branches on
each cell, giving `(FPC18)`.  Away from `L`, the denominator is positive,
so the quotient bound is equivalent to `(FPC20)`.  At `y in L`, both
`N(y)` and `D(y)` vanish.  Continuity of the two quadratics shows that the
same polynomial inequality on the closed cell is equivalent to all
directional limiting inequalities.  End proof.

Thus a proposed rational bound `T` has a finite exact certificate: enumerate
the active sites, construct the rational polytopes `(FPC14)`, and certify
one rational quadratic polynomial as nonpositive on each polytope.  This is
a standard exact semialgebraic decision problem.  It can be attacked by
face recursion and rational quadratic programming, or certified by sums of
squares with exact rational residual checking.

## 4. Algebraicity and stationary-value pencils

The finite certificate has a useful formal consequence.

**Corollary 4 (algebraicity).**  `C_circ(A)^2` is a real algebraic number.
For rational `T`, the assertions `C_circ(A)^2<=T` and
`C_circ(A)^2<T` are decidable by exact real algebraic arithmetic.

**Proof.**  The set of `T` satisfying all the finitely many statements
`(FPC20)` is semialgebraic over `Q`, by quantifier elimination for real
closed fields.  It is the ray `[C_circ(A)^2,infinity)`.  An endpoint of a
one-dimensional semialgebraic set defined over `Q` is real algebraic.  The
same quantifier elimination decides comparison with a rational `T`.  End
proof.

There is also a more concrete candidate calculation.  Let `F` be a face of
a cell and write its affine hull as

`y=y_0+Ux`, `x in R^d`.                                          `(FPC21)`

On this affine hull write

`q_ell(y)=x^TQx+2b^Tx+alpha`,
`r_(c,a)(y)=x^TRx+2d^Tx+beta`.                                  `(FPC22)`

Every relative-interior stationary value `t=q_ell(y)/r_(c,a)(y)` satisfies

`det M_F(t)=0`,                                                   `(FPC23)`

where

`M_F(t)=[[Q-tR, b-td],[(b-td)^T, alpha-t beta]].`                 `(FPC24)`

Indeed stationarity and `q_ell-t r_(c,a)=0` are exactly

`M_F(t)[x,1]^T=0`.                                               `(FPC25)`

Enumerating faces, solving the univariate pencils `(FPC23)`, and retaining
only feasible points gives all nondegenerate candidates.  At a common zero
`y in L`, the missing directional candidates are the generalized Rayleigh
values of the two quadratic tangent forms; equivalently one may use the
real blow-up of `P` at the finitely many points `P intersect L`.  The
polynomial criterion `(FPC20)` handles these degenerate points without any
special case, so `(FPC23)` is an optimization aid rather than an additional
hypothesis.

## 5. Relation to the projective charts

For every exact projective `SL_3(Z)` chart, all matrices and lattices in
this note are integral or rational.  The previous exact results provide:

1. the real Hodge bounds controlling `H_A`;
2. the discriminant gluing and harmonic pullback controlling the possible
   denominator wells; and
3. the integral lift sequence controlling their paired numerators.

Theorem 3 now supplies the last fixed-chart step:

`integral phase repair`
` = finite paired Voronoi refinement`
` = finite rational quadratic certification.`                     `(FPC26)`

At harmonic rank two, such as level `53`, the small-well classes are already
described by a binary quadratic lattice.  The remaining exact comparison
map from the compact Ash--Grayson--Green function lattice to the HAP
cellular metric would therefore produce a finite list of cells and
quadratic pencils whose maximum is the exact level-`53` repair constant.

The family-level obstruction is unchanged and now especially sharp: a TRUE
proof needs a uniform reason that the finite certificates `(FPC20)` admit
one bound `T` over the selected charts.  The fixed-chart nonlinear
optimization itself is no longer an open-ended search.
