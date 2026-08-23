---
rg: 2
id: sparse-dyadic-iwahori-packets-have-a-uniform-boundary
kind: claim
title: Bounded-sparse deep dyadic Iwahori packets have a uniform restriction boundary
distinct_from:
  pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss: that uses the complete Plancherel conductor table and excludes arbitrary mixtures of regular packets; this treats arbitrary selected irreducibles but assumes only finitely many occupied conductor depths.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that is the rank-three SL3 depth-shift estimate with a one-eighth loss; this is the rank-one Dogon--Vigdorovich diagram and gives the sharp last-layer two-thirds fixed-space ceiling from the characteristic-two coadjoint orbits.
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that invokes a fixed finite restriction diagram and its unspecified Hoffman constant; this gives a depth-independent mismatch floor for sparse supports even when their occupied depths tend to infinity.
---

Let `G_a=SL_2(Z/2^a Z)`, `a>=3`, and let `B`, `sigma`, `N_a`, and
`M_a` be the upper/opposite Iwahori data of
`pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss`.  If `pi`
is any representation of `G_a` all of whose irreducible constituents have
minimal congruence conductor exactly `a`, then

```text
dim Fix(pi(u(2^(a-1)))) <= (2/3) dim(pi).                (SDI1)
```

The same bound holds for the last lower-root element and hence in the
opposite coordinate.  The constant `2/3` is sharp at the last-layer orbit
level.

Now let `Pi_+`, `Pi_-` be equal-dimensional pure dyadic vertex packets and
decompose their positive-conductor parts into exact conductor bands.  Assume
all occupied bands have conductor at least `3`, and that the union of the
two conductor supports has cardinality at most `K`.  Write `rho,eta` for
their upper and opposite edge restrictions and

```text
L=sum_(theta in Irr(B/(N_A intersection M_A))) dim(theta)
       |mult_theta(rho)-mult_theta(eta)|,                (SDI2)
```

after inflating to any common level `A`.  Then

```text
L/d >= 2/(4^K-1).                                       (SDI3)
```

Equivalently their maximal common edge subrepresentation has normalized
dimension at most `1-1/(4^K-1)`.  Selberg `(tau)` therefore gives the
generator-defect floor

```text
max_(s in S_B)||rho(s)V-V eta(s)||_2
 >= kappa_B/sqrt(4^K-1)                                 (SDI4)
```

for every unitary comparison `V`.

Consequently no sequence of single irreducibles, principal/supercuspidal
types, or packets occupying a uniformly bounded number of growing
two-power conductors can have normalized restriction mismatch tending to
zero.  A surviving selected non-Plancherel enemy must occupy an unbounded
number of conductor depths.  More precisely, its common-subrepresentation
coupling `c_(a,b)` must carry at least one third of every upper exact-depth
band (up to unmatched mass) strictly upward to opposite depth `b>a`, and
at least one third of every opposite band strictly upward in the reverse
coordinate, to upper depth `a>b`.  Thus it is necessarily a bidirectional,
cross-conductor diffuse tower; a one-way chain of sparse local types cannot
be the obstruction.

