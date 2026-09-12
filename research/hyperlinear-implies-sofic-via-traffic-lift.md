---
rg: 2
id: hyperlinear-implies-sofic-via-traffic-lift
kind: route
title: Lift the microstate to a branching graph law and realize it by an action
target: hyperlinear-implies-sofic
requires:
  - traffic-branching-rounding-hierarchy
  - permutation-traffic-is-simultaneous-fixed-points
---

Let `G` be hyperlinear with finite window `F` and table `T`.  A microstate of
sufficient accuracy is lifted, by `traffic-branching-rounding-hierarchy`, to a
positive graph-indexed law whose connected branching moments are within `o(1)`
of the canonical values and which satisfies the positivity and reflection
constraints of a permutation traffic law.

`permutation-traffic-is-simultaneous-fixed-points` is what makes that sentence
have content: it identifies the canonical values — a connected branching
moment of a genuine finite action is the density of roots fixed simultaneously
by the cycle words of the test graph — so the target of the lift is explicit
rather than an unknown limiting parameter, and matching those values on enough
test graphs is exactly the statement that the law is (approximately) carried by
a finite action on a finite set.  Realizing that law by an actual action and
reading off the permutations gives a sofic model of `T`.

The realization step is the part of this route that is asserted rather than
argued, and it is where the route can fail without its premises failing: a law
can satisfy every tested branching constraint and still not be carried by a
finite set, exactly as a positive functional can satisfy every tested moment
constraint and not be a measure.  Recording it here rather than as a third
premise reflects that the source dossier gives no candidate realization
theorem; anyone working the route should promote it to a claim as soon as they
have a shape for it.
