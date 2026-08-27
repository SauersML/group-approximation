# Nonlinear circle repair has an exact paired-discriminant formula

Date: 2026-08-11

## Purpose

`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md` bounds circle repair by a real
singular-value constant times the integral carry constant `Theta`.
`INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` then gives an exact formula for
`Theta` in terms of the discriminant gluing of the saturated range and
cycle lattices.  The present note removes the remaining slack at the first
step: the **optimal nonlinear circle-repair constant itself** is an exact
finite discriminant-envelope problem.

There are two useful consequences.

1. The previous factors `1+Theta` and `1+||A||C` improve respectively to
   `Theta` and `sqrt(1+(||A||C)^2)`.
2. In a projective chart the dangerous harmonic dual lattice has the exact
   pullback description

   `Q^# = H intersect (Z^m+W)`.                       `(NDR1)`

   Thus the rank-two `p=53` lattice can be lifted by a rational
   two-variable congruence calculation; an integral basis of the enormous
   full cycle lattice is unnecessary.

This is an exact structural reduction, not yet a uniform bound on the
selected `SL_3(Z)` family.  The remaining numerator problem is visible
explicitly in the formulas below.

## 1. The exact nonlinear constant

Let `E,F` be finite-dimensional real Hilbert spaces with full lattices
`E_Z,F_Z`, and let

`A:E->F`, `A(E_Z) subset F_Z`.                        `(NDR2)`

Put

`W=ran(A)`, `L=W intersect F_Z`,                      `(NDR3)`

and assume `0<dim(W)<dim(F)`.  Let

`A^+:W->ker(A)^perp`                                 `(NDR4)`

be the inverse of the restriction of `A` to `ker(A)^perp`.  It induces the
ellipsoidal norm

`||v||_(A,+)=||A^+v||` for `v in W`.                 `(NDR5)`

For `y in W`, write

`d_(A,L)(y)=min_(ell in L)||y-ell||_(A,+)`.          `(NDR6)`

Define the optimal additive circle-repair constant

`C_circ(A)=sup_(x notin A^(-1)(F_Z))`
`             rep_A(x)/def_A(x)`,                   `(NDR7)`

with `rep_A` and `def_A` as in
`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md`.

**Lemma 1 (exact quotient norm).**

`rep_A(x)=d_(A,L)(Ax)`.                              `(NDR8)`

Consequently

`C_circ(A)=sup_(y in W minus L)`
`             d_(A,L)(y)/dist(y,F_Z)`.              `(NDR9)`

**Proof.**  Fix `ell in L`.  Among all `v in E` satisfying

`Av=Ax-ell`,                                         `(NDR10)`

the unique vector of least norm is `A^+(Ax-ell)`.  Replacing `x` by
`x-v` gives an exact point, and every exact point arises from some
`ell in L`.  Taking the minimum over `ell` proves `(NDR8)`.  The map
`A:E->W` is surjective, so taking the supremum over `x` is the same as
taking it over `y=Ax`; this proves `(NDR9)`.  End proof.

The quotient in `(NDR9)` is `L`-periodic.  It is therefore enough to take
the supremum over one compact fundamental domain of `L`, with its finitely
many points of `L` omitted.

## 2. The paired-discriminant envelope

Set `Lambda=F_Z`, with its Euclidean metric, and

`K=Lambda intersect W^perp`.                         `(NDR11)`

Use the dual lattices, discriminant groups, and canonical gluing

`gamma:D_K=K^#/K -> D_L=L^#/L`                      `(NDR12)`

from `INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md`.  For `c in D_K` and
`y in W`, define

`d_(gamma c)(y)=min{||y-a||:a in L^#, a+L=gamma(c)}`. `(NDR13)`

Let `rho_K(c)` be the shortest radius of the coset `c` in `K^#`.

**Theorem 2 (exact nonlinear discriminant formula).**  For every `y in W`,

`dist(y,Lambda)^2`
` =min_(c in D_K)(d_(gamma c)(y)^2+rho_K(c)^2).`     `(NDR14)`

Therefore

`C_circ(A)`
` =sup_(y in W minus L)`
`   d_(A,L)(y) /`
`   sqrt(min_(c in D_K)`
`     (d_(gamma c)(y)^2+rho_K(c)^2)).`               `(NDR15)`

Thus the nonlinear repair problem is exactly the upper envelope of the
ellipsoidal distance to `L` divided by the lower envelope of finitely many
paired discriminant wells.

**Proof.**  Unimodular gluing gives the disjoint orthogonal decomposition

`Lambda`
` =disjointUnion_(c in D_K)`
`   ({a in L^#:a+L=gamma(c)}`
`    +{u in K^#:u+K=c}).`                            `(NDR16)`

For `y in W`, `a in W`, and `u in W^perp`, orthogonality gives

`||y-(a+u)||^2=||y-a||^2+||u||^2`.                  `(NDR17)`

Inside a fixed glued component in `(NDR16)`, the two representatives vary
independently by elements of `L` and `K`.  Minimizing `(NDR17)` first in
that component and then over `c` proves `(NDR14)`.  Combine `(NDR14)` with
Lemma 1 to obtain `(NDR15)`.  End proof.

Formula `(NDR15)` is finite in the discriminant direction and continuous
in a fundamental domain of `L`.  It is exact even when the closest integer
carry changes discontinuously: those changes are precisely the walls where
two of the quadratic wells in `(NDR14)` agree.

## 3. Sharp comparison with carry transversality

Let `sigma_+(A)` be the least positive singular value and let `Theta(W)` be
the carry constant.  The discriminant formula for `Theta` is

`Theta(W)^2`
` =max(1,max_(0!=c in D_K)`
`   (1+rho_L(gamma c)^2/rho_K(c)^2)).`                `(NDR18)`

**Theorem 3 (multiplicative factor comparison).**

`sqrt(Theta(W)^2-1)/||A||`
` <= C_circ(A) <= Theta(W)/sigma_+(A).`               `(NDR19)`

Equivalently, any inequality `rep_A<=C def_A` implies

`Theta(W)<=sqrt(1+(||A||C)^2)`.                      `(NDR20)`

**Proof of the upper bound.**  Fix `y in W`, and choose a closest
`z=a+u in Lambda`, with `a in L^#`, `u in K^#`, and common discriminant
class `c`.  Put `t=||y-a||` and `s=||u||`.  If `c=0`, then `a in L` after
translation and

`dist(y,L)<=t<=sqrt(t^2+s^2)`.                       `(NDR21)`

If `c!=0`, then

`dist(y,L)<=t+rho_L(gamma c)`
` <=t+sqrt(Theta(W)^2-1) rho_K(c)`
` <=t+sqrt(Theta(W)^2-1) s`
` <=Theta(W)sqrt(t^2+s^2)`.                          `(NDR22)`

The last line is Cauchy--Schwarz.  Since `z` is closest,
`sqrt(t^2+s^2)=dist(y,Lambda)`.  Finally

`d_(A,L)(y)<=sigma_+(A)^(-1)dist(y,L)`,              `(NDR23)`

and `(NDR9)` proves the upper bound.

**Proof of the lower bound.**  Fix `0!=c in D_K`.  Choose shortest
representatives `a in gamma(c)` and `u in c`.  Gluing implies
`z=a+u in Lambda`.  At the point `y=a`,

`dist(a,Lambda)<=||a-z||=rho_K(c)`,                 `(NDR24)`

whereas

`d_(A,L)(a)>=rho_L(gamma c)/||A||`.                 `(NDR25)`

Insert `(NDR24)--(NDR25)` into `(NDR9)`, maximize over nonzero `c`, and
use `(NDR18)`.  This proves the lower bound and `(NDR20)`.  End proof.

The previous factorization theorem had the bounds
`(1+Theta)/sigma_+` and `1+||A||C`.  Theorem 3 shows that those additive
ones were only triangle-inequality slack; no new obstruction sits there.
For a family with bounded `||A||` and uniformly positive `sigma_+`, uniform
nonlinear circle repair is still exactly equivalent to uniform `Theta`,
now with the purely multiplicative comparison `(NDR19)`.

## 4. Harmonic pullback without the full cycle lattice

Return to one projective chart.  Let `Sigma subset K` be the spherical
lattice generated by the bounded lifted templates, and put

`S=span_R(Sigma)`, `H=K_R intersect S^perp`,
`Q=pi_H(K)`.                                         `(NDR26)`

As in `TRUE_PROJECTIVE_HARMONIC_SYSTOLE.md`,

`Q^#=K^# intersect H`.                               `(NDR27)`

Write `K_H=K intersect H` for the integral harmonic lattice.

**Theorem 4 (harmonic pullback and paired lift).**

`Q^#={u in H:there exists a in W with u+a in Lambda}`
`   =H intersect (Lambda+W).`                        `(NDR28)`

For `u in Q^#`, choose `a in W` such that `u+a in Lambda` and set

`eta(u)=a+L in D_L`.                                 `(NDR29)`

Then `eta` is a well-defined homomorphism with

`ker(eta)=K_H`.                                      `(NDR30)`

It therefore induces an injection

`bar(eta):D_H:=Q^#/K_H -> D_L`,                     `(NDR31)`

and the diagram

`D_H -------> D_K`
` |             | gamma`
`bar(eta)       v`
` +----------> D_L`                                  `(NDR32)`

commutes, where the top map is `u+K_H |-> u+K`.

**Proof.**  Proposition 1 of the discriminant note gives
`K^#=p_K(Lambda)`.  For `u in H subset K_R=W^perp`, the equality
`p_Kz=u` is equivalent to `z-u in W`.  This proves `(NDR28)`.

If both `u+a` and `u+a'` are integral, then
`a-a' in Lambda intersect W=L`, so `(NDR29)` is well defined.  It is
plainly additive.  If `eta(u)=0`, change `a` by an element of `L` so that
`a=0` modulo the same integral lift.  Then `u in Lambda intersect H=K_H`.
The converse is immediate, proving `(NDR30)--(NDR31)`.  Finally, the two
components `a,u` of the same integral vector define the canonical gluing,
which proves `(NDR32)`.  End proof.

The point of `(NDR28)` is computational as well as conceptual.  If `R` is
an exact rational basis matrix for the harmonic space and `B` is a rational
basis matrix for `W`, then

`Q^#={Rx:there exist y and z in Z^m with Rx+By=z}`.  `(NDR33)`

After clearing denominators, `(NDR33)` is an ordinary Smith/Hermite lattice
preimage problem in `dim(H)` variables.  It never asks for a basis of
`K=ker(A^T) intersect Z^m`.

## 5. Exact localization of the dangerous classes

Let `B_0` be the maximum norm of the bounded spherical templates.  For
`c in D_H`, define the rank-`dim(H)` harmonic radius

`rho_H(c)=min{||u||:u in Q^#, u+K_H=c}`.             `(NDR34)`

Let `i(c)` be its image in `D_K`.

**Theorem 5 (small classes are exactly harmonic).**

`rho_K(i(c))<1/B_0` if and only if `rho_H(c)<1/B_0`, `(NDR35)`

and in that case

`rho_K(i(c))=rho_H(c)`.                              `(NDR36)`

Moreover, every class of `D_K` whose shortest radius is less than `1/B_0`
lies in the image of `D_H`.  Its paired range class is exactly
`bar(eta)(c)`.

**Proof.**  Always `rho_K(i(c))<=rho_H(c)`.  If either side is less than
`1/B_0`, choose a shortest representative on the side known to be small.
Proposition 12 of the discriminant note forces every such shortest
representative in `K^#` to be orthogonal to `Sigma`, hence to lie in `H`.
Two harmonic representatives of the same `D_K` class differ by
`K intersect H=K_H`.  Therefore the two minima agree.  The same localization
puts every small `D_K` class in the image of `D_H`; commutativity of
`(NDR32)` identifies its range class.  End proof.

This theorem is the exact denominator/numerator coupling missing from the
earlier harmonic-systole note.  Below the fixed spherical threshold, the
terms in the carry formula are precisely

`1+rho_L(bar(eta)c)^2/rho_H(c)^2`, `0!=c in D_H`,    `(NDR37)`

with `rho_H(c)<1/B_0`.  No unspecified full-cycle discriminant class remains
in this sector.

## 6. Rank two at `p=53`

The exact computation in `experiments/sl3_projective_carry_results.md`
gives `dim(H)=2` at `p=53`.  Once an exact rational basis of the numerical
harmonic plane is recovered, Theorem 4 reduces all dangerous lattice data
to rank two.

Let the columns of `V` be a `Z`-basis of `Q^#`, and let the columns of `U`
be a `Z`-basis of `K_H`.  There is an integral nonsingular `2 x 2` matrix
`M` with

`U=VM`, `D_H ~= Z^2/MZ^2`.                          `(NDR38)`

If `u=U alpha` represents a class of `D_H`, and
`G_H=U^T U`, then

`rho_H(u+K_H)^2`
` =min_(n in Z^2)(alpha+n)^T G_H(alpha+n).`          `(NDR39)`

This is an exact binary quadratic closest-vector problem.  If
`u+a=z in Z^m` is the lift supplied by `(NDR33)`, then

`rho_L(bar(eta)(u))=dist(a,L)`.                      `(NDR40)`

The regulator is obtained from the same two-column basis:

`Reg(Q^#)=sqrt(det(V^T V))`,
`Reg(Q)=1/sqrt(det(V^T V)).`                         `(NDR41)`

Thus the next `p=53` calculation is no longer “compute a huge integral
kernel.”  It is:

1. recover an exact rational basis `R` for the two-dimensional Hodge kernel;
2. solve the two-variable lattice pullbacks `(NDR33)` for `Q^#` and
   `K_H=H intersect Z^m`;
3. enumerate the finite quotient `(NDR38)` and solve the binary forms
   `(NDR39)`;
4. solve the paired saturated-range CVPs `(NDR40)` only for the classes
   below the spherical threshold.

Steps 1--3 determine the harmonic regulator and dual systole exactly.
Step 4 is the still-live numerator decoder.  A uniform theorem must either
bound those paired radii over all projective primes or exhibit a sequence
for which the ratios in `(NDR37)` diverge.

`TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md` gives the exact next reduction.
The numerator is the extra squared norm in the short exact sequence
`0->L->M_Sigma->Q^#->0`; a bounded integral section of this sequence bounds
all harmonic paired radii at once.  In rank two, the optimal nonlinear lift
distortion and the norm of a linear section differ by at most `4/sqrt(3)`.

## 7. Status

The exact implications now are

`nonlinear circle repair`
` <=> paired discriminant envelope (NDR15)`
` <=> bounded carry distortion under the Hodge bounds (NDR19).`

For projective charts, every possible denominator collapse is further
identified with the finite harmonic gluing subgroup `(NDR31)`, and at
`p=53` that subgroup is computable from a rank-two rational pullback.

What remains is genuinely arithmetic: uniformly control the paired range
radii in `(NDR37)` and the nonsmall spherical-sector classes.  The real
Hodge problem and the nonlinear nearest-carry bookkeeping are no longer
mixed together.

`TRUE_FINITE_PAIRED_DISCRIMINANT_CERTIFICATE.md` removes the remaining
continuous optimization on each fixed chart.  On a compact fundamental
polytope, only finitely many numerator lattice sites and paired
discriminant wells are active.  Their common Voronoi refinement is rational
polyhedral, and an asserted bound `C_circ(A)^2<=T` is equivalent to a finite
family of exact quadratic nonpositivity tests on those cells.  In
particular, the optimal squared constant is always real algebraic.

## 8. Exact rank-one computational calibration

The paired envelope is already nontrivial for a primitive rank-one map

`A:R->R^2`, `A(t)=(pt,qt)`, `gcd(p,q)=1`.             `(NDR42)`

Put `N=p^2+q^2`.  Then

`L=Z(p,q)`, `K=Z(-q,p)`, `|D_K|=N`.                  `(NDR43)`

Index a cycle discriminant class by `j mod N`.  If `(r,s) in Z^2`
satisfies

`j=-qr+ps mod N`,                                    `(NDR44)`

its paired range index is

`h(j)=pr+qs mod N`.                                  `(NDR45)`

This is well defined and bijective.  If

`bar(j)=min(j mod N,-j mod N)`,                       `(NDR46)`

then

`rho_K(j)^2=bar(j)^2/N`,                             `(NDR47)`

and `(NDR14)--(NDR15)` become

`dist((pt,qt),Z^2)^2`
` =min_(j mod N)(`
`    N dist(t,h(j)/N+Z)^2+bar(j)^2/N),`              `(NDR48)`

`C_circ(A)^2`
` =sup_(t mod Z)`
`   dist(t,Z)^2`
`   /min_(j mod N)(`
`      N dist(t,h(j)/N+Z)^2+bar(j)^2/N).`            `(NDR49)`

The lower envelope in `(NDR49)` is piecewise quadratic with rational
breakpoints.  `experiments/integral_carry_exact_repair_formula.sage`
constructs the gluing map, checks `(NDR48)` with exact rational arithmetic,
and maximizes `(NDR49)` by subdividing at all envelope crossings.  The
stored certificate is
`experiments/integral-carry-exact-repair-formula.json`.

| column `(p,q)` | `|D_K|` | `Theta^2` | `C_circ(A)^2` | optimizing `t` |
| --- | ---: | ---: | ---: | ---: |
| `(1,1)` | 2 | 2 | `1/2` | `0` (directional limit) |
| `(1,2)` | 5 | 5 | `1` | `1/2` |
| `(2,3)` | 13 | 26 | `2` | `2/5` |
| `(2,5)` | 29 | 145 | `5` | `5/12` |
| `(3,5)` | 34 | 170 | `5` | `5/13` |

All 1,060 sampled distance identities have exact rational error zero.  In
the last four examples, the sharp upper bound in `(NDR19)` is attained
exactly:

`C_circ(A)^2=Theta(W)^2/(p^2+q^2).`                  `(NDR50)`

For `(1,1)`, the inequality is strict: its right side is `1`, while the
exact constant is `1/2`.  Thus Theorem 3 is sharp even in primitive
rank-one families, but the full paired envelope `(NDR15)` contains strictly
more information than `Theta` and the singular values on an individual
chart.
