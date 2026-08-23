---
rg: 2
id: bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair
kind: claim
title: Pure dyadic Iwahori pairs of bounded conductor admit uniform linear repair
distinct_from:
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that is uniform over unbounded odd levels because the edge image is full; this treats the complementary pure two-primary packets, with a constant depending on a fixed conductor bound.
  iwahori-local-global-defect-question: that asks for one modulus over all vertex representations and all two-adic depths; this closes only the union of finitely many pure dyadic quotient diagrams.
  iwahori-fractional-transport-integralization: that is the unbounded-type operator matching theorem; this uses finite branching-matrix rounding after imposing a conductor bound.
---

For every integer `A>=0` there is `K_A<infinity` such that the following
holds.  Let `pi_+,pi_-` be exact same-dimensional representations of the two
modular vertices in the Dogon--Vigdorovich Iwahori diagram.  Suppose each
factors through a pure dyadic quotient

```text
SL_2(Z/2^a), SL_2(Z/2^b),             0<=a,b<=A.       (BDI1)
```

Then there is an exactly compatible same-dimensional pair
`pi~_+,pi~_-` with

```text
D(pi_+,pi_-)<=K_A def(pi_+,pi_-).                       (BDI2)
```

Consequently a counterexample made from exact pure dyadic vertex packets
must have unbounded two-adic conductor.  Together with the odd-congruence
linear theorem, this rules out both growing odd level and every bounded
pure dyadic window as the source of failure.

One unbounded family is now excluded without any conductor cutoff.
`pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss` computes the
complete upper/opposite joint conductor table. Its off-diagonal support is
two exponentially weighted rays with Cheeger constant `1/2`, so even an
arbitrary finite mixture of amplified regular congruence packets has at most
one-half common edge mass. Selberg `(tau)` turns this into a depth-uniform
Iwahori defect floor. Thus the surviving unbounded tower must exploit
selected non-Plancherel irreducibles, not regular cross-conductor routing.

The dependence on `A` is the exact remaining issue.  Index-three branching
alone does not make it uniform: fixed-degree integer incidence matrices can
have Hoffman constants diverging along arbitrarily long paths (a unit-slope
integer ramp has `L^1` distance quadratic in path length from the constant
kernel while its edge residual is only linear).  For the actual Iwahori
tower one must therefore control the restriction monoids coherently across
depth, or exploit the conductor-shift relations; bounded branching and the
three-coset core intersection do not supply that control.

Even adding a uniform Hilbert-space angle does not close this gap.
`l2-angle-does-not-imply-l1-integer-hoffman` gives bounded-degree integral
incidence maps with a uniform nonzero `L^2` singular value but logarithmically
diverging real and integer `L^1` Hoffman constants.  Therefore the existing
cuspidal/Eisenstein angle and Selberg `(tau)` cannot be converted formally
into physical-rank rounding.  A positive depth-uniform theorem must prove an
`L^1` flow bound using the specific dyadic restriction ring, not only its
`L^2` spectrum.

The failure of the tempting analytic replacement is already exact at level
two.  `three-coset-frame-saturation-is-not-pair-functorial` gives the actual
opposite-Iwahori packet in which a common polar edge line saturates to zero
(or the whole standard plane) on one vertex and to the same line on the
other.  Amplification makes the input defect tend to zero.  The fixed-level
repair above succeeds by changing that one paid vertex block; separate
conditional expectations or core intersections cannot avoid the joint
multiplicity rounding step.
