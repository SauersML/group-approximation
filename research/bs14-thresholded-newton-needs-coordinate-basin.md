---
rg: 2
id: bs14-thresholded-newton-needs-coordinate-basin
kind: claim
title: Thresholded BS14 residuals enter Newton only after an operator-norm coordinate-basin theorem
distinct_from:
  iwahori-newton-closes-near-sector: that attempted an HS-metric Taylor integration and was invalidated; this states the valid mixed-norm theorem and the exact thresholding hypothesis it still lacks.
  normalized-hs-taylor-remainder-is-not-dimension-free: that gives the rank-one Hessian counterexample; this uses operator-norm truncation to remove that counterexample but shows residual norm is not coordinate proximity.
  bs14-residual-polar-data-build-active-dilation: that asks for the full reverse dilation; this isolates the low-singular-value Newton gate after the high carrier has hypothetically been handled.
---

Let the two cubic residuals have total normalized energy `e`, and for a
threshold `theta>0` let `P_i^hi` be the spectral projection of `|D_i|` on
`(theta,infinity)`.  Then

```text
(rank P_1^hi+rank P_2^hi)/d <= e/theta^2,             (TNB1)
||D_i(1-P_i^hi)||_op<=theta.                          (TNB2)
```

Thus choosing `theta->0` with `e/theta^2->0` isolates a sublinear-rank high
carrier and a low residual with small operator norm.

The valid Newton statement is the following mixed-norm theorem.  Let
`F` be the Iwahori compatibility map, let `rho` be an exact congruence point,
and quotient the tangent space by the true common-conjugation modes.  Write
`sigma_0` for the established level-independent lower singular value of
`DF(rho)`, and `L` for the fixed-word Hessian constant in

```text
||F''[Z,Z]||_2 <= L ||Z||_op ||Z||_2.                 (TNB3)
```

If a tuple `pi` lies in the same torsion stratum and has a normal coordinate
`Z` from the exact locus with

```text
||Z||_op <= sigma_0/(2L),                             (TNB4)
```

then

```text
dist_2(pi,C) <= (2/sigma_0)||F(pi)||_2.               (TNB5)
```

This follows from Taylor expansion:
`||F(pi)||_2 >= sigma_0||Z||_2-L||Z||_op||Z||_2`.
The constant is independent of dimension, congruence level, and
multiplicity.

However, `(TNB2)` does not imply `(TNB4)`.  The former is a small value in
the **codomain** of the nonlinear word map.  It neither supplies a nearby
zero nor integrates the discarded high singular matrix to a perturbation of
`X`.  Spectrally replacing `D_i` by `D_i(1-P_i^hi)` does not produce a new
group tuple whose residual is that replacement.  That integrability is the
reverse boundary-dilation problem itself.

There is no tangent-sequence obstruction at exact congruence points:
`iwahori-uniform-infinitesimal-rigidity` proves `sigma_0>0` uniformly, after
quotienting the genuine tangent modes.  Hence any failure of the threshold
program is global/nonlinear, not a sequence of inverse derivatives tending
to infinity.

The exact remaining low-part hypothesis is therefore an operator-norm
coordinate-basin assertion:

> after an energy-controlled realization of the high carriers, every tuple
> with low cubic residual operator norm at most `theta` lies at operator-norm
> distance `o_theta(1)` from some exact moving-level congruence atom, modulo
> its true tangent modes and small-rank torsion changes.

No current Iwahori or character-rigidity theorem proves this.  If supplied,
`(TNB5)` corrects the low part and the sublinear high carrier can be handled
flexibly.  Without it, active/passive spectral thresholding is a ledger, not
a reverse construction.

The exact global meaning of this coordinate-basin assertion is now recorded
in `authenticated-core-union-basin-is-relative-liftability`.
After the core has been authenticated, small defects give an exact relative
homomorphism only in the matrix ultraproduct.  Entering the union of moving
endpoint orbits is equivalent to lifting that homomorphism by coordinate
congruence representations, with `o(d)` boundary padding.  Selberg controls
the normal coordinate **after** such a lift; it does not supply the lift by
compactness.

The tempting order-three spectral shortcut is now closed precisely by
`bs14-cubic-rounding-leaves-relative-core-basin`: writing
`A=XS^2`, `B=XRS`, each cubic rounds in operator norm with constant `1/2`,
but the independently rounded pair no longer has relative product
`S^(-2)RS` and need not recover one common dihedral involution.  Hence the
coordinate-basin hypothesis is relative BS-core stability, not ordinary
torsion spectral stability.

`bs14-hs-stability-does-not-supply-relative-op-basin` rules out the next
formal shortcut.  The rounded relative product is an operator-norm
approximate BS implementer, but the established solenoid theorem repairs it
only in normalized HS.  Exact BS cores can be `o(1)` apart in normalized HS
and `sqrt(3)` apart in operator norm on one scalar packet, so that correction
does not enter the mixed-norm Newton tube.

`long-bs14-packets-defeat-invariant-op-thresholding` shows that flexible
outlier removal does not repair this formally.  There are irreducible
length-`m` exact cores which are `O(m^(-1/2))` apart in HS but uniformly
operator-far.  A fixed threshold sees only boundedly many high coordinate
lines, yet the BS-invariant hull of any one is the entire packet and exact
type-balancing padding costs `m`.  Thus the high/low singular cut cannot be
promoted to an exact-core cut before Newton without a new non-invariant
reconnection and joint repair theorem.
