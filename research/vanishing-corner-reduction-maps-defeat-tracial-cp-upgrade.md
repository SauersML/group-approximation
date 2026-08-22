---
rg: 2
id: vanishing-corner-reduction-maps-defeat-tracial-cp-upgrade
kind: claim
title: Vanishing-corner reduction maps defeat trace-rigid growing-positivity upgrades to complete positivity
distinct_from:
  maslov-central-regular-lifts-have-diverging-positive-order: that constructs growing-order positive lifts in the actual tracial quotient; this gives an explicit coordinate-matrix calibration showing why trace uniqueness cannot upgrade them to complete positivity.
  strict-psd-regularization-has-no-uniform-hs-affine-error-bound: that is a cone-angle example for positive matrices; this is a unital trace-preserving k-positive map on a full matrix factor, with exact failure at level k+1.
  property-t-alone-cannot-correct-tracial-choi-lifts: that uses a global Kazhdan counterexample; this isolates the matrix-order obstruction on an asymptotically invisible corner.
---

**ESTABLISHED.** For integers `1<=k<r`, define

```text
R_(k,r)(X)=(k Tr(X) I_r-X)/(kr-1),       X in M_r.      (VCR1)
```

Then `R_(k,r)` is unital, trace-preserving, and `k`-positive, but it is not
`(k+1)`-positive and hence is not completely positive.

This obstruction can be hidden on a normalized-Hilbert--Schmidt invisible
corner of a matrix **factor**.  Put `D=N+r`, write `M_D` in `N+r` blocks, and
let

```text
Phi_(N,k,r)(X)
 =diag(X_00,R_(k,r)(X_11)).                              (VCR2)
```

Thus `(VCR2)` first pinches away the off-diagonal blocks.  It is unital,
normalized-trace preserving, and `k`-positive but not `(k+1)`-positive.  For
every block-diagonal contraction `X=X_00 direct-sum X_11`,

```text
||Phi_(N,k,r)(X)-X||_(2,D) <= 2 sqrt(r/D).               (VCR3)
```

Choose, for example, `k=floor(sqrt(r))` and `N=r^2`.  Then `k->infinity`,
`k/D->0`, `(VCR3)->0`, and complete positivity still fails at the explicit
level `k+1`.

This is the required coordinate-scale calibration for the Maslov lane.
Even on full matrix factors with unique trace, the conjunction

- exact trace preservation;
- positivity order tending to infinity; and
- asymptotic `2`-norm identity on every fixed block-diagonal generator tuple

does not imply complete positivity.  If the large block carries any fixed
arithmetic tuple, arbitrary behavior on the `r/D=o(1)` corner changes every
fixed word and relator defect by only `O(sqrt(r/D))`; character rigidity and
bounded-word centrality cannot see the matrix-order witness living there.

This does not construct a non-cp restriction on the specific finite Maslov
generator system: the `(k+1)`-positivity witness uses an escaping
`(k+1)`-dimensional matrix amplification.  It proves the precise no-go that
arithmetic character rigidity, finite-factor trace uniqueness, and
generator-level normalized-HS control **alone** cannot upgrade the lifts in
`maslov-central-regular-lifts-have-diverging-positive-order`.  A positive
Maslov argument must force the escaping Choi witness to intersect the fixed
root/Weyl operator system, rather than merely control its scalar trace or
bounded word moments.

