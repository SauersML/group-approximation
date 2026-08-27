# Induced finite-image representations obey identity-gap domination

Date: 2026-08-11

## Purpose

The universal TRUE reduction compares the classical moved-point domination
constant with the normalized-character domination constant.  After the
irreducible reduction, a possible obstruction is a sequence of irreducible
unitary representations of unbounded degree.

This note closes a substantial finite-image subclass.  An induced
finite-image representation already carries a canonical finite coset action.
The only loss in comparing their two defects is the smallest normalized trace
gap between the identity and a nonidentity inducing block.  Consequently:

* a uniform inducing identity gap gives the required character domination;
* finite-image monomial representations of uniformly bounded phase exponent
  cannot obstruct TRUE; and
* more generally, induced finite-image representations with uniformly bounded
  block dimension and exponent cannot obstruct TRUE.

The proof is exact and dimension-free in the number of inducing cosets.

## Setup

Let `F` be a finitely generated free group, let `R subset F` be finite, and
put

`P=F/normal_closure_F(R)`.                              `(IIG1)`

Fix `w in Rad_sof(P)`.  By the linear sofic-radical inequality in
`TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md`, there is a finite constant
`C_cl` such that every nonempty finite `F`-action `rho` satisfies

`d_rho(w) <= C_cl sum_(r in R) d_rho(r)`,              `(IIG2)`

where `d_rho(g)` is the moved-point fraction of `g`.

Let `H <= F` have finite index, let

`tau:H -> U(k)`                                        `(IIG3)`

be a unitary representation with finite image, and set

`sigma=Ind_H^F(tau)`, `d=[F:H]`, `K=ker(tau)`.         `(IIG4)`

Thus `K` is normal and finite index in `H`, and hence is finite index in
`F`.  Write

`delta_sigma(g)=1-Re tr_(dk)(sigma(g))`.               `(IIG5)`

The finite image of `tau` gives a strictly positive identity gap

`eta(tau)=min_(h in H:tau(h)!=I)`
`         (1-Re tr_k(tau(h))) > 0`,                    `(IIG6)`

with the minimum over the empty set interpreted as `+infinity`.  Put

`eta_0(tau)=min(1,eta(tau))`.                          `(IIG7)`

Here and below `tr_k` denotes normalized trace.

## The exact coset comparison

**Theorem 1 (induced identity-gap comparison).**  For every `g in F`,

`eta_0(tau) d_(F/K)(g) <= delta_sigma(g)`
`                            <= 2 d_(F/K)(g)`.         `(IIG8)`

Here `F/K` denotes the finite left-coset `F`-action; normality of `K` in
`F` is not required.

**Proof.**  Choose representatives `x` of the left cosets `F/H`.  The
normalized induced-character formula is

`tr_(dk)(sigma(g))`
` = (1/d) sum_(xH:g xH=xH) tr_k(tau(x^(-1) g x)).`    `(IIG9)`

It is useful to rewrite the defect as an average of local defects over all
`xH in F/H`.  A nonfixed base coset contributes `1`.  If `xH` is fixed,
put `h=x^(-1)gx in H`; its contribution is

`1-Re tr_k(tau(h))`.                                  `(IIG10)`

Now consider the projection of finite `F`-sets

`F/K -> F/H`.                                         `(IIG11)`

The fiber over `xH` consists of the `[H:K]` points `xaK`, with `a in H/K`.
If `xH` is not fixed by `g`, none of these fiber points is fixed.  If `xH`
is fixed and `h=x^(-1)gx`, then

`g xaK=xaK  iff  a^(-1) h a in K`.                   `(IIG12)`

Because `K` is normal in `H`, condition `(IIG12)` holds for every `a` if
`h in K`, and for no `a` otherwise.  Thus the local contribution to the
moved fraction of `F/K` is exactly

* `1` on a nonfixed base coset;
* `0` on a fixed base coset with `tau(h)=I`; and
* `1` on a fixed base coset with `tau(h)!=I`.

The corresponding local character defect is respectively `1`, `0`, and a
number in `[eta(tau),2]`.  Averaging the local inequalities proves `(IIG8)`.
End proof.

The point of `(IIG8)` is that neither comparison constant depends on the
coset degree `[F:H]`.  All representation-specific loss is isolated in the
identity gap of the inducing block.

## Radical domination consequence

**Theorem 2 (induced finite-image domination).**  Under `(IIG1)--(IIG7)`,

`delta_sigma(w)`
` <= (2 C_cl/eta_0(tau)) sum_(r in R) delta_sigma(r).` `(IIG13)`

**Proof.**  Apply the upper half of `(IIG8)`, the classical radical
inequality `(IIG2)` to the finite action `F/K`, and then the lower half of
`(IIG8)`:

`delta_sigma(w)`
` <= 2 d_(F/K)(w)`
` <= 2 C_cl sum_(r in R)d_(F/K)(r)`
` <= (2 C_cl/eta_0(tau)) sum_(r in R)delta_sigma(r).`

End proof.

**Corollary 3.**  A sequence

`sigma_n=Ind_(H_n)^F(tau_n)`                          `(IIG14)`

of finite-image representations can have unbounded normalized-character
domination ratio only if

`eta(tau_n) -> 0`                                     `(IIG15)`

along a subsequence.

Indeed, any uniform positive lower bound for the identity gaps makes the
right side of `(IIG13)` uniform.  Growth of the total induced dimension or
of the coset degrees `[F:H_n]` alone is harmless.

## Bounded block dimension and exponent

The identity gap has a simple uniform lower bound when the inducing images
have bounded exponent and dimension.

**Lemma 4.**  Suppose `k<=k_0`, and every element of the finite group
`tau(H)` has order dividing `M`, where `M>=2`.  Then

`eta(tau) >= (1-cos(2 pi/M))/k_0`.                    `(IIG16)`

**Proof.**  If `U=tau(h)!=I`, every eigenvalue of `U` is an `M`-th root of
unity and at least one is nontrivial.  Every nontrivial `M`-th root `zeta`
satisfies

`1-Re(zeta) >= 1-cos(2 pi/M)`.                        `(IIG17)`

All eigenvalue contributions are nonnegative, so normalized trace gives

`1-Re tr_k(U) >= (1-cos(2 pi/M))/k`
`              >= (1-cos(2 pi/M))/k_0`.              `(IIG18)`

Taking the minimum proves the lemma.  End proof.

Combining Theorem 2 and Lemma 4 gives the explicit uniform estimate

`delta_sigma(w)`
` <= 2 C_cl max(1,k_0/(1-cos(2 pi/M)))`
`       * sum_(r in R)delta_sigma(r).`                 `(IIG19)`

In particular, a transitive finite-image monomial representation is induced
from a one-dimensional finite-order character of a finite-index subgroup.
If all its phases have exponent dividing a fixed `M`, then `k_0=1` in
`(IIG19)`.  Therefore growing permutation degree with bounded phase exponent
cannot produce the universal TRUE obstruction.

## What this removes, and what remains

This theorem is stronger than merely observing that a fixed finite-image
coefficient module is harmless.  The subgroup `H`, its index, the finite
image, and the induced degree may all vary.  Only the normalized trace gap
from a nonidentity inducing block must remain uniform.

After the irreducible reduction, a hypothetical obstruction must therefore
avoid this theorem in at least one of the following ways:

1. it is not induced from finite-image blocks of finite-index subgroups;
2. its inducing identity gaps tend to zero, for example through unbounded
   phase exponent or unbounded block dimension; or
3. it has infinite image and admits no finite-image reduction preserving the
   normalized relator and witness defects.

Thus `(IIG13)` does not prove the full hyperlinear-implies-sofic theorem.
It does prove a new exact exclusion principle: **imprimitivity and growing
coset degree are not themselves sources of the gap; vanishing internal
identity gap is necessary.**
