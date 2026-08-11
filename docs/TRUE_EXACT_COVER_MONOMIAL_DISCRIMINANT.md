# Exact-cover monomial domination is a marked discriminant ratio

Date: 2026-08-11

## Purpose

`TRUE_INDUCED_IDENTITY_GAP_DOMINATION.md` controls induced finite-image
representations whenever the inducing identity gap stays positive.  The
remaining monomial escape has phases of unbounded order, where that gap can
vanish.

On an exact finite action of the presented quotient, there is a different
description with no identity-gap loss.  Every lifted loop of a sofic-radical
word is an integral cellular boundary.  Therefore its phase holonomy factors
over the integers through the relator phase holonomies.  This note proves
that the optimal normalized-character domination constant on that chart is,
up to universal sharp chordal/geodesic comparisons, exactly the Lipschitz
constant of this factor map.  Its denominator has the paired-discriminant
formula, while its numerator is evaluation against the canonical radical
filling vectors.

This is the direct bridge from the universal radical-character problem to
the integral-carry/discriminant geometry.  It does not assume bounded phase
exponent.

## 1. Phase maps on an exact finite chart

Let

`P=<S | R>`                                                `(ECM1)`

be a finite presentation, let `w in Rad_sof(P)`, and let `X` be a nonempty
finite `P`-set.  The associated Schreier presentation complex has integral
cochain map

`A_X=d_X^1:C^1(X,R)->C^2(X,R)`.                       `(ECM2)`

In cellular coordinates, `C^1` is the space of phase labels on the directed
generator edges, while `C^2` has one coordinate for every `(x,r) in X times
R`.  Let

`B_X=B_(w,X):C^1(X,R)->R^X`                           `(ECM3)`

be evaluation around the lifted `w`-loop at each vertex.

Both maps have integral matrices.  They induce torus homomorphisms, denoted
by bars,

`bar(A_X):C^1(X,R/Z)->C^2(X,R/Z)`,
`bar(B_X):C^1(X,R/Z)->(R/Z)^X`.                       `(ECM4)`

Give the two target spaces the normalized squared geodesic norms

`||u||_(0,T)^2=(1/|X|)sum_(x in X) dist(u_x,Z)^2`,    `(ECM5)`

`||v||_(2,T)^2=(1/|X|)sum_(x in X,r in R)`
`                         dist(v_(x,r),Z)^2`.         `(ECM6)`

On the phase-label space use, similarly,

`||theta||_(1,T)^2=(1/|X|)sum_(x in X,s in S)`
`                              dist(theta_(x,s),Z)^2.` `(ECM6a)`

The sum over relators is deliberately not divided by `|R|`; it matches the
total relator defect in the universal domination constant.

## 2. Integral factorization by radical fillings

Since `w` belongs to the sofic radical, it lies in the commutator subgroup
of every finite-index stabilizer.  The integral radical-filling theorem in
`FALSE_RADICAL_FILLING_DISCRIMINANT.md` therefore supplies, for every
`x in X`, an integral two-chain `z_x` such that

`A_X^* z_x=b_(w,x)`.                                  `(ECM7)`

Let `Z_X:C^2(X,R)->R^X` be the integral matrix whose `x`-th row is `z_x`.

**Theorem 1 (integral holonomy factorization).**

`B_X=Z_X A_X` over `Z`.                               `(ECM8)`

In particular,

`ker(bar(A_X)) <= ker(bar(B_X))`,                     `(ECM9)`

and there is a well-defined torus homomorphism

`Tbar_X:im(bar(A_X))->(R/Z)^X`,
`Tbar_X(bar(A_X)theta)=bar(B_X)theta`.                `(ECM10)`

It is independent of all choices of integral fillings.

**Proof.**  For every real one-cochain `theta`, adjointness and `(ECM7)`
give

`(B_X theta)_x=<b_(w,x),theta>`
` =<A_X^*z_x,theta>=<z_x,A_Xtheta>`
` =(Z_XA_Xtheta)_x`.                                  `(ECM11)`

This proves `(ECM8)`, hence `(ECM9)--(ECM10)`.  If `Z_X'` comes from
different fillings, then `(Z_X-Z_X')A_X=0`, so both matrices induce the
same map on `im(bar(A_X))`.  End proof.

The factorization is stronger than a qualitative compactness assertion: it
is integral, so every finite cyclic phase table is sent to a phase table of
the same denominator.

## 3. Exact additive domination constant

Define the marked torus Lipschitz constant

`Lambda_(w,X)`
` =sup_(0!=y in im(bar(A_X)))`
`       ||Tbar_X(y)||_(0,T)/||y||_(2,T)`.             `(ECM12)`

Theorem 1 and any integral filling matrix give

`Lambda_(w,X)<=||Z_X||_(2->0)`,                       `(ECM13)`

so the constant is finite on every fixed chart.

**Theorem 2 (exact additive phase domination).**

`Lambda_(w,X)^2`
` =sup_(theta:bar(A_X)theta!=0)`
`   ||bar(B_X)theta||_(0,T)^2`
`   /||bar(A_X)theta||_(2,T)^2`.                     `(ECM14)`

Consequently the optimal additive inequality on the chart is exactly

`||bar(B_X)theta||_(0,T)^2`
` <=Lambda_(w,X)^2||bar(A_X)theta||_(2,T)^2`.         `(ECM15)`

**Proof.**  Equation `(ECM10)` identifies the numerator with
`||Tbar_X(y)||_(0,T)` for `y=bar(A_X)theta`.  Every point in the image has
such a preimage, so the two suprema are identical.  Inequality `(ECM13)`
follows by choosing a closest integral lift `a` of `y`: the vector `Z_Xa`
is a lift of `Tbar_X(y)`, and hence

`||Tbar_X(y)||_(0,T)<=||Z_Xa||_0`
` <=||Z_X||_(2->0)||a||_2`.                         `(ECM16)`

End proof.

## 4. Exact normalized-character interpretation

A phase table `theta in C^1(X,R/Z)` defines monomial generator matrices

`U_s e_x=exp(2 pi i theta(s,x)) e_(sx)`.              `(ECM17)`

They extend to a unitary representation of the free group on `S`.  Because
the underlying permutation action factors through `P`, every `r in R` acts
diagonally.  The radical word `w` also fixes every vertex: the action map
`P->Sym(X)` has finite, hence sofic, image and must kill `w`.

Thus, with

`e(t)=1-cos(2 pi t)`,                                 `(ECM18)`

the normalized character defects are exactly

`delta_theta(w)=(1/|X|)sum_x e((bar(B_X)theta)_x)`,   `(ECM19)`

`sum_(r in R)delta_theta(r)`
` =(1/|X|)sum_(x,r)e((bar(A_X)theta)_(x,r)).`         `(ECM20)`

Let `C_mon(w,X)` be the optimal constant in

`delta_theta(w)<=C_mon(w,X)sum_(r in R)delta_theta(r)` `(ECM21)`

over all phase tables.  Use `0/0=0`; Theorem 1 guarantees that zero
relator defect also gives zero word defect.

**Theorem 3 (chordal/geodesic equivalence).**

`(4/pi^2)Lambda_(w,X)^2 <= C_mon(w,X)`
`             <=(pi^2/4)Lambda_(w,X)^2`.             `(ECM22)`

**Proof.**  On the principal interval `[-1/2,1/2]`,

`8 dist(t,Z)^2 <= e(t) <= 2 pi^2 dist(t,Z)^2`.        `(ECM23)`

Apply the upper estimate to `(ECM19)`, Theorem 2, and then the lower
estimate to `(ECM20)` to obtain the upper half of `(ECM22)`.  Reversing
the two estimates shows that every constant in `(ECM21)` is at least
`(4/pi^2)Lambda_(w,X)^2`.  End proof.

Therefore uniform normalized-character domination on exact finite charts
is equivalent to

`sup_(X finite P-set)Lambda_(w,X)<infinity`.          `(ECM24)`

There is no dependence here on the orders of the phases.

## 5. Full circle repair bounds every marked radical map

Let `C_circ(A_X)` be the optimal nonlinear circle-repair constant of
`A_X`, with the normalized source and target norms used above:

`dist(theta,ker(bar(A_X)))`
` <=C_circ(A_X)||bar(A_X)theta||_(2,T).`              `(ECM24a)`

Let `ell(w)` be the length of the displayed word in the generators and
their inverses.

**Theorem 4 (repair-to-radical domination).**

`Lambda_(w,X)<=||B_X||_(1->0) C_circ(A_X)`
`             <=ell(w) C_circ(A_X)`
`             <=ell(w) Theta(A_X)/sigma_+(A_X).`     `(ECM24b)`

Consequently

`C_mon(w,X)`
` <=(pi^2/4)ell(w)^2 C_circ(A_X)^2`
` <=(pi^2/4)ell(w)^2 Theta(A_X)^2/sigma_+(A_X)^2.`   `(ECM24c)`

**Proof.**  Given a phase table `theta`, choose `theta_0` in
`ker(bar(A_X))` with

`||theta-theta_0||_(1,T)`
` <=C_circ(A_X)||bar(A_X)theta||_(2,T)+epsilon.`      `(ECM24d)`

The integral factorization gives `bar(B_X)theta_0=0`.  Therefore

`||bar(B_X)theta||_(0,T)`
` <=||B_X||_(1->0)||theta-theta_0||_(1,T).`           `(ECM24e)`

If `w=t_1...t_ell`, its real evaluation map is a sum of `ell` signed
coordinate pullbacks.  Each pullback is a contraction in normalized `L2`,
because the current vertex is obtained from `x` by a permutation.  Hence

`||B_X||_(1->0)<=ell(w)`.                             `(ECM24f)`

Let `epsilon` tend to zero.  This proves the first two bounds in `(ECM24b)`.
The exact nonlinear repair estimate `(NDR19)` gives

`C_circ(A_X)<=Theta(A_X)/sigma_+(A_X)`,               `(ECM24g)`

and Theorem 3 then gives `(ECM24c)`.  End proof.

For a fixed property-`(T)` presentation, `sigma_+(A_X)` is uniformly
positive over exact finite charts.  Thus a uniform carry bound
`sup_X Theta(A_X)<infinity` proves uniform normalized-character domination
for **every** radical word and every phase order on those charts.  This is
the precise positive role of the Hodge certificate and the integral-carry
program: the Hodge gap controls real repair, while `Theta` is the entire
remaining nonlinear loss.

The converse need not hold for one marked word.  Formula `(ECM31)` below
can be bounded because its particular radical filling vectors annihilate
the dangerous discriminant classes even when the full unmarked repair
constant grows.

## 6. Marked paired-discriminant formula

Put

`W_X=ran_R(A_X)`, `L_X=W_X intersect Z^(X times R)`, `(ECM25)`

`K_X=W_X^perp intersect Z^(X times R)`.              `(ECM26)`

Let

`gamma_X:D_(K_X)->D_(L_X)`                           `(ECM27)`

be the canonical unimodular gluing.  The real map

`T_X:W_X->R^X`, `T_X(A_Xtheta)=B_Xtheta`,             `(ECM28)`

is well defined by `(ECM8)` and maps `L_X` into `Z^X`.  It therefore
induces `Tbar_X`.

For each vertex, let

`q_(w,x)=(A_X^dagger)^*b_(w,x) in L_X^#`             `(ECM29)`

be the canonical coexact radical filling.  Then

`(T_X y)_x=<q_(w,x),y>` for y in W_X.                `(ECM30)`

**Theorem 5 (exact marked discriminant ratio).**

`Lambda_(w,X)^2`
` =sup_(y in W_X minus L_X)`
`   dist(T_Xy,Z^X)^2 /`
`   min_(c in D_(K_X))(`
`      d_(gamma_X c)(y)^2+rho_(K_X)(c)^2).`          `(ECM31)`

Here the distances in `(ECM31)` use the ordinary cellular Euclidean norms,
so `Z^(X times R)` is unimodular and the canonical discriminant gluing
applies literally.  The factors `1/|X|` in `(ECM5)--(ECM6)` occur on both
sides of the ratio and cancel.  The term `d_(gamma_X c)(y)` is the distance
from `y` to the indicated coset of `L_X` in `L_X^#`.

**Proof.**  A point of `im(bar(A_X))` has a lift `y in W_X`, unique modulo
`L_X`.  Its ambient torus distance from zero is

`dist(y,Z^(X times R))`.                              `(ECM32)`

The exact paired-discriminant identity `(NDR14)` in
`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` writes the square of
`(ECM32)` as the denominator of `(ECM31)`.  Equations `(ECM28)--(ECM30)`
identify the numerator with the torus norm of `Tbar_X(y)`.  Substitute both
identities into `(ECM12)`.  End proof.

Formula `(ECM31)` is the promised exact connection.  The denominator is the
same lower envelope of paired range/cycle discriminant wells that governs
integral carry repair.  The numerator is not an unspecified decoder norm:
it is the simultaneous pairing against the canonical radical filling
vectors `(ECM29)`.

## 7. Consequences and remaining boundary

Theorems 3 and 4 prove the following exact exclusion principle.

**Corollary 6.**  Suppose the marked ratios `(ECM31)` are uniformly bounded
over a family of exact finite `P`-sets.  Then no sequence of monomial
representations whose underlying permutation actions belong to that family
can have unbounded radical-character domination ratio, regardless of phase
orders.

A simpler sufficient condition is a choice of integral filling matrices
with

`sup_X ||Z_X||_(2->0)<infinity`.                     `(ECM33)`

The exact constant `(ECM31)` can remain bounded even when every convenient
integral filling has larger full operator norm, because it only measures the
induced map on the relator-image torus and includes the ambient carry wells.

Combined with `TRUE_INDUCED_IDENTITY_GAP_DOMINATION.md`, the monomial
boundary is now:

1. bounded phase exponent is harmless even when the underlying finite
   permutation action only approximately satisfies the presentation;
2. arbitrary phase exponent on an exact finite `P`-set is governed exactly
   by the marked discriminant ratio `(ECM31)`; and
3. the still-uncontrolled overlap consists of unbounded phase exponent on
   nonexact permutation charts, together with possible growth of `(ECM31)`
   over exact charts.

This does not solve the universal TRUE theorem.  It identifies precisely
where the nonlinear integral-carry geometry enters the normalized-character
gate, and it separates that arithmetic issue from approximate permutation
repair.
