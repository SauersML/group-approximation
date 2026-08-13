# Ioana rigidity reduces the Schreier moments to a finite integral-chart test

Date: 2026-08-11

## 1. Outcome and scope correction

The actual induced Weyl construction has one remaining scalar gate.  For the
finite Schreier transition cocycle at clock order `M_k`, let

`R_(*,k) = max_s (average_x |r_k(x,s)|_(M_k)^2)^(1/2)`,

`A_(*,k) = max_s average_x |a_k(x,s)|_(M_k)`,             `(IC1)`

where the maximum is over the fixed positive generators.  The exact seam
criterion is

`R_(*,k)=o(M_k)`,

`A_(*,k)=o(M_k)`,

`R_(*,k) A_(*,k)=o(M_k)`.                                `(IC2)`

This note records a strong sufficient condition for `(IC2)`.  Suppose the
entire tower of growing finite transition cocycles is obtained by reducing
one cocycle with values in a **fixed countable group**, and the finite-stage
representative supplied by rigidity lies in a coordinate-tame chart.  Then Ioana's
cocycle superrigidity theorem makes that cocycle finite-stage up to
cohomology.  A cylinder approximation to the transfer function gives genuine
finite-level Schreier gauges for which

`R_(*,k)=O(1)` and `A_(*,k)=O(1)`.                         `(IC3)`

Consequently all three limits in `(IC2)` vanish.

For the Baumslag--Solitar clock tower, coordinate tameness is automatic
after one constant conjugation.  The intended fixed target is

`B = BS(1,q) = <h,c | c h c^(-1)=h^q>`, `q=p+1`,          `(IC4)`

and the finite targets are its metacyclic quotients

`B_k = <h_k,c_k | h_k^(p^(k+1))=c_k^(p^k)=1,`
`                    c_k h_k c_k^(-1)=h_k^q>`.            `(IC5)`

Thus the unresolved problem is sharply localized:

> Do the actual Kun--Thom induced Schreier cocycles admit a coherent
> `B`-valued lift whose reductions are the finite transition cocycles?

The theorem below says that a positive answer finishes the three-number
screen **provided the action is one to which the quoted cocycle-rigidity
theorem applies**.  It does **not** construct that lift.  A fixed element of
`BS(1,p+1)` can have a nonintegral horocyclic coordinate whose centered
reductions remain linear in `M_k`, but finite-stage factorization leaves only
finitely many such denominators and one stable-letter conjugation clears all
of them.  Applying cocycle rigidity to each finite level separately, or
replacing `B` by the uncountable profinite inverse limit of the `B_k`, does
not prove the result.

There is a further load-bearing restriction.  Ioana's theorem
`arXiv:0805.2998` is stated for a **free ergodic profinite action**.  The
natural inverse limit of finite coset actions used by the Schreier tower is
not free: it retains conjugates of the amenable stabilizer.  Therefore that
coset tower cannot be substituted below merely because it is profinite and
ergodic.  One first needs either a free profinite realization carrying the
same coherent transition cocycle, or a cocycle-rigidity theorem whose
hypotheses genuinely cover this nonfree coset action.  Neither bridge is
presently supplied.

## 2. Abstract setup

Let `A` be a countable property `(T)` group with a **free ergodic** profinite action

`A curvearrowright X = inverse_limit_n X_n`,             `(IC6)`

in a setting covered by Ioana's cocycle superrigidity theorem.  Let `S` be a
fixed finite generating set.

Let `B` be a fixed countable group and let

`pi_k:B -> B_k`                                          `(IC7)`

be homomorphisms to finite groups.  Put `M_k -> infinity`.  For each `k`,
assume that a chosen coordinate section on `B_k` assigns centered coordinates

`r_k(u), a_k(u) in [-M_k/2,M_k/2] cap Z`.                 `(IC8)`

Call a finite set `F subset B` **coordinate-tame** if there is
`C_F<infinity` such that, for all sufficiently large `k` and every `b in F`,

`|r_k(pi_k(b))|<=C_F` and `|a_k(pi_k(b))|<=C_F`.          `(IC8a)`

For the natural quotients `(IC4)--(IC5)`, this holds for fixed elements whose
horocyclic coordinates are integers.  It is false for arbitrary fixed
Baumslag--Solitar elements; Section 4 gives the exact denominator
obstruction.

Let

`beta:A times X -> B`                                    `(IC9)`

be a measurable cocycle.  Assume that the actual finite transition cocycle
at the selected finite stage is the reduction

`beta_k(s,x)=pi_k(beta(s,x))`,                            `(IC10)`

in the following precise sense: `beta_k` factors through some finite quotient
of `X`, and passing to a deeper finite quotient pulls it back to the actual
Schreier bundle used at level `k`.  This is the **coherent countable lift
hypothesis**.

Changing the Schreier transversal is the usual finite gauge operation

`beta_k^u(s,x)=u_k(sx) beta_k(s,x) u_k(x)^(-1)`.           `(IC11)`

## 3. The finite-stage moment theorem

**Theorem 1 (coordinate-tame coherent lift implies bounded moments).**  In
the setup above, suppose the finite set of positive-generator values of an
Ioana finite-stage representative is coordinate-tame.  Then there are a
cofinal sequence of finite quotients and finite gauges `u_k` for which the
transition coordinates of `(IC11)` satisfy `(IC3)`.  In particular, all
three limits `(IC2)` hold.

### Proof

Apply Ioana's cocycle superrigidity theorem to the single `B`-valued cocycle
`beta`.  Since `B` is countable, there exist a measurable map

`phi:X -> B`,                                            `(IC12)`

an index `n_0`, and a cocycle `beta':A times X -> B` factoring through
`X_(n_0)` such that

`beta'(s,x)=phi(sx) beta(s,x) phi(x)^(-1)`.               `(IC13)`

The set

`F={beta'(s,x):s in S, x in X_(n_0)}`                    `(IC14)`

is finite and is coordinate-tame by hypothesis.  Hence there is a constant `C`, independent of
`k`, such that both centered coordinates of `pi_k(F)` have absolute value at
most `C` for all sufficiently large `k`.

There is one technical point: `phi` need not factor through any fixed finite
quotient.  Reduce it modulo `B_k`:

`phi_k=pi_k composed_with phi:X -> B_k`.                  `(IC15)`

This is a measurable finite-valued function.  Cylinder functions are dense
in measure on the profinite probability space.  Therefore, for every
`delta_k>0`, there are an index `n(k)>=n_0` and a function

`u_k:X_(n(k)) -> B_k`                                    `(IC16)`

whose pullback agrees with `phi_k` outside a set `E_k` of measure at most
`delta_k`.

Fix `s in S`.  On every point outside

`E_k union s^(-1)E_k`,                                  `(IC17)`

the finite gauge `(IC16)` transforms the reduction of `beta` exactly into
the reduction of `beta'`.  Hence both transition coordinates there have
absolute value at most `C`.  The exceptional set has measure at most
`2 delta_k`, and every centered coordinate has absolute value at most
`M_k/2`.  Consequently

`R_(s,k)^2 <= C^2 + delta_k M_k^2/2`,                    `(IC18)`

`A_(s,k)   <= C   + delta_k M_k`.                        `(IC19)`

The same estimates hold simultaneously for all `s in S`; if desired replace
`2 delta_k` by `2|S|delta_k` after using one common exceptional set.

Choose, for example,

`delta_k=M_k^(-4)`.                                     `(IC20)`

After passing to the finite quotient `X_(n(k))`, `(IC16)` is an honest
finite Schreier gauge.  Equations `(IC18)--(IC20)` give

`R_(*,k)<=C+o(1)`, `A_(*,k)<=C+o(1)`.                   `(IC21)`

Since `M_k -> infinity`,

`R_(*,k)/M_k -> 0`,

`A_(*,k)/M_k -> 0`,

`R_(*,k)A_(*,k)/M_k -> 0`.                              `(IC22)`

This proves the theorem.  End proof.

The use of a deeper quotient `X_(n(k))` is harmless for the induced model:
the old transition system is merely pulled back, while the new cylinder
gauge is now a legitimate finite transversal change.  No pointwise
approximation of `phi` is required.

## 4. The exact Baumslag--Solitar denominator obstruction

Write

`BS(1,q) = Z[1/q] semidirect Z`,                         `(IC23)`

using coordinates `(u,a)`, where `a` is the stable-letter exponent and `u`
is the horocyclic coordinate.  Reduction to `(IC5)` sends `a` modulo `p^k`
and sends `u` modulo `M_k=p^(k+1)`; here `q=p+1` is invertible modulo `M_k`.

For every fixed `(u,a)`, the centered stable-letter coordinate is eventually
the fixed integer `a`.  Thus a finite-stage `B`-valued cocycle automatically
gives `A_*=O(1)`.

The horocyclic coordinate behaves differently.  Write a nonzero fixed
rational as

`u=m/q^d`, with `m in Z` and `d>=0`.                     `(IC24)`

Let `r_k` be its centered reduction modulo `M_k`.  Then

`q^d r_k = m+t_k M_k`                                   `(IC25)`

for an integer `t_k`.  If `r_k/M_k -> 0`, division of `(IC25)` by `M_k`
shows `t_k -> 0`.  Since `t_k` is integral, it is eventually zero, and then
`q^d r_k=m`.  Therefore `q^d` divides `m`.

After writing `u` in lowest `q`-denominator, this proves the dichotomy

`|r_k|=O(1)  if u in Z`,

`liminf_k |r_k|/M_k > 0  if u notin Z`.                 `(IC26)`

Indeed, in the second case `t_k` is eventually nonzero and `(IC25)` gives,
up to the vanishing term `m/M_k`,

`|r_k|/M_k >= 1/q^d-o(1)`.                              `(IC27)`

Now suppose Ioana has replaced the coherent lift by a cocycle `beta'`
factoring through the fixed finite set `X_(n_0)`.  Write the positive-generator
values as

`beta'(s,x)=(u_(s,x),a_(s,x))`.                         `(IC28)`

Because every cell of `X_(n_0)` has fixed positive measure, `(IC26)` gives
an exact finite-stage alternative:

* if every `u_(s,x)` is integral, then the coordinate compatibility
  hypothesis of Theorem 1 holds and all three seam statistics vanish;
* if some `u_(s,x)` is nonintegral and its value is the relevant Weyl
  coefficient coordinate, then `R_*/M_k` has a positive lower bound, so the
  seam criterion fails in that gauge.

One may still change `beta'` by a gauge on the finite set `X_(n_0)`.
Consequently the residual question after Ioana rigidity is the following
finite problem:

> Is the finite `BS(1,q)`-valued cocycle cohomologous to one whose
> positive-generator transition values all have integral horocyclic
> coordinates?

This is substantially smaller than optimizing transversals independently at
every `k`.  For a general countable target it is a genuine extra problem;
countable-target cocycle superrigidity alone does not answer it.

In the present Baumslag--Solitar target, however, this finite problem always
has a solution.  Because `(IC28)` has finite range, choose `D>=0` so that

`q^D u_(s,x) in Z`                                      `(IC29)`

for every `s in S` and `x in X_(n_0)`.  Conjugate the whole finite-stage
cocycle by the constant transfer `c^D`.  The semidirect-product law gives

`c^D (u,a) c^(-D)=(q^D u,a)`.                           `(IC30)`

Thus every relevant horocyclic coordinate becomes integral, while every
stable-letter coordinate is unchanged.  Moreover `q^D=1 mod p`, so
conjugation fixes the order-`p` subgroup carrying the marked Bockstein fold.
The new finite set of transition values is coordinate-tame without changing
the marked order-`p` holonomy.

**Corollary 2 (coherent Baumslag--Solitar lift implies the three limits).**
If the actual finite Schreier transition tower is obtained by reducing one
`BS(1,p+1)`-valued cocycle as in `(IC9)--(IC10)`, and `r_k` is the centered
reduction of its horocyclic coordinate, then there are cofinal finite levels
and genuine Schreier gauges for which `(IC2)` holds.

**Proof.**  Apply Ioana, clear the finitely many denominators by `(IC29)--`
`(IC30)`, and apply Theorem 1.  End proof.

## 5. Consequence for the Weyl seam

Combine Corollary 2 with
`FALSE_INDUCED_WEYL_SEAM_MOMENT_CRITERION.md` and its endpoint correction
`FALSE_INDUCED_WEYL_SEAM_ENDPOINT_AUDIT.md`.  There are seam widths
`L_k|M_k` such that for every fixed positive generator the squared normalized
Hilbert--Schmidt discrepancy is bounded by

`8 pi^2 R_(*,k)^2 L_k^2/M_k^2 + 8 A_(*,k)/L_k`,          `(IC31)`

and tends to zero.  The already constructed order-`p` Bockstein holonomy is
unchanged by the block-diagonal seam gauge.

Therefore a coherent Baumslag--Solitar lift supplies exactly the missing
global transition estimate.  Subject to the already isolated
finite-module and amalgam compatibility identifications, it places the
FALSE construction in the final ultraproduct assembly stage.

## 6. Why three tempting shortcuts do not suffice

### 6.1 Levelwise Ioana rigidity

For every `k`, the finite target `B_k` is countable, so one can apply Ioana
to `beta_k`.  This produces some finite factorization stage `n_k`.  It gives
no uniform control on `n_k`, on the transfer function, or on the centered
coordinates after gauge.  The values can escape to order `M_k` as `k`
grows.  Levelwise rigidity alone therefore proves none of `(IC2)`.

### 6.2 The profinite inverse-limit target

The compatible family `(beta_k)_k` naturally defines a cocycle with values
in the profinite inverse limit

`B_hat=inverse_limit_k B_k`.                            `(IC32)`

Except in degenerate cases, `B_hat` is uncountable.  Ioana's theorem quoted
here concerns countable target groups.  It cannot simply be applied to
`(IC32)`.

More importantly, even a finite-stage statement in the compact target would
not by itself control the Archimedean sizes of centered exponents.  An
element of `B_hat` may have reductions whose centered coordinates are a
positive fraction of `M_k`.

### 6.3 Direct-limit embeddings

There are natural embeddings between some finite clock groups obtained by
raising generators to `p`th powers.  A fixed nontrivial element at a low
level then appears at higher levels with exponents proportional to a power
of `p`.  This is the wrong orientation for `(IC2)`.  The useful hypothesis
is reduction from fixed integer data in `B`, not inclusion into a growing
direct limit.

## 7. Exact remaining construction problem

The next theorem to prove is not another clock identity and not another
abstract cocycle reformulation.  It is one of the following two concrete
statements.

1. **Free coherent lift form.**  Construct a free ergodic profinite
   `A`-space `X` and a single measurable cocycle
   `beta:A times X -> BS(1,p+1)` whose reductions are, after pullback, the
   actual Kun--Thom finite Schreier transition systems.  Corollary 2 then
   supplies the integral-horocyclic gauge automatically.  A coherent
   cocycle on the nonfree coset inverse limit alone does not authorize the
   quoted theorem.

2. **Direct moment form.**  Construct finite transversals in the actual
   transition systems satisfying `(IC2)` without passing through a
   countable lift.

The first statement implies the second by Theorem 1.  If neither statement
holds, the failure must be exhibited as a genuine escape of the finite
transition cocycles in the profinite completion: no gauge can keep both Weyl
coordinates sublinear in precisely the three senses `(IC2)`.

At present neither alternative has been proved.  Thus this note is a
rigorous reduction of the real Schreier problem, not a proof of FALSE.

## 8. Subsequent primitive-holonomy exclusion

The conditional theorem above is correct, but its sufficient hypothesis is
not available for the exact primitive scalar principal bundle.
`FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md` proves that whenever a
transition coordinate is the difference of a primitive potential

`r(tx)=r(x)+1 mod M_k`,

property `(T)` forces some fixed generator to have mean centered coordinate
at least

`(kappa^2/(4 pi)) M_k`.

Thus the finite-stage integral-chart conclusion `(IC3)` contradicts the
prescribed primitive holonomy.  For the actual scalar bundle, the coherent
countable lift, compatibility with the primitive finite reductions, and the
integral-horocyclic gauge cannot all hold.

Accordingly, option 1 in Section 7 is retained only as a diagnostic
trichotomy: a failed component must be identified.  It is no longer a live
positive construction for the primitive scalar seam.  The surviving route
must change the tangent/Fourier representation with the base point or use
higher-incidence cancellation, so that the Kazhdan-forced holonomy is not one
of the scalar Weyl transition coordinates.
