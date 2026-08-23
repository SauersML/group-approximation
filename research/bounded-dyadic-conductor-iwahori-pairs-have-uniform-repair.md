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

This bounded-window statement is now subsumed by
`pure-dyadic-iwahori-pairs-have-uniform-linear-repair`, which obtains one
constant over the full unbounded two-adic tower from Clifford character-slot
conservation.

One unbounded family is now excluded without any conductor cutoff.
`pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss` computes the
complete upper/opposite joint conductor table. Its off-diagonal support is
two exponentially weighted rays with Cheeger constant `1/2`, so even an
arbitrary finite mixture of amplified regular congruence packets has at most
one-half common edge mass. Selberg `(tau)` turns this into a depth-uniform
Iwahori defect floor. Thus the surviving unbounded tower must exploit
selected non-Plancherel irreducibles, not regular cross-conductor routing.

The former concern about dependence on `A` was genuine at the level of
abstract bounded-degree incidence matrices: their Hoffman constants can
diverge along long paths. The later Clifford slot theorem supplies the
missing arithmetic input for this particular tower, rather than deriving
uniformity from bounded branching alone.

Adding a uniform Hilbert-space angle did not formally close this gap.
`l2-angle-does-not-imply-l1-integer-hoffman` gives bounded-degree integral
incidence maps with a uniform nonzero `L^2` singular value but logarithmically
diverging real and integer `L^1` Hoffman constants. Thus the existing
cuspidal/Eisenstein angle and Selberg `(tau)` could not be converted
formally into physical-rank rounding. The later positive theorem uses the
specific newest-layer character slots, not only the `L^2` spectrum.

The failure of the tempting analytic replacement is already exact at level
two.  `three-coset-frame-saturation-is-not-pair-functorial` gives the actual
opposite-Iwahori packet in which a common polar edge line saturates to zero
(or the whole standard plane) on one vertex and to the same line on the
other.  Amplification makes the input defect tend to zero.  The fixed-level
repair above succeeds by changing that one paid vertex block; separate
conditional expectations or core intersections cannot avoid the joint
multiplicity rounding step.
