---
rg: 2
id: hyperlinear-nonsofic-from-kt-ce-stabilizer
kind: route
title: A trace-free commutation stabilizer for the Kun--Thom subgroup makes the double hyperlinear and nonsofic
target: hyperlinear-nonsofic-group
requires: [kt-subgroup-is-a-ce-commutation-stabilizer, ce-stabilizer-criterion-needs-no-trace, kt-q2-double-hyperlinear-iff-relative-embeddable, kt-pair-group-double-is-nonsofic, kun-thom-nonsofic-wreath]
---

1. `kun-thom-nonsofic-wreath` (Theorem E) makes `G` residually finite, hence
   hyperlinear, which is the standing hypothesis of
   `ce-stabilizer-criterion-needs-no-trace`.
2. A witness for `kt-subgroup-is-a-ce-commutation-stabilizer` gives, by that
   criterion, relative embeddability of `L(Gamma) <= L(G)` over the scalars.
3. By `kt-q2-double-hyperlinear-iff-relative-embeddable`, the double
   `D = G *_Gamma G` is hyperlinear.
4. By `kt-pair-group-double-is-nonsofic`, `D` is not sofic.

So `D` is a hyperlinear nonsofic group.

**Scope, stated so the route is not mistaken for a reduction to something
weaker.** The first prerequisite is *equivalent* to hyperlinearity of `D`, by
the criterion and step 3. What the route adds is the admissible search space:
a witness may live in any Connes-embeddable target, under any trace, for any
not-necessarily-injective homomorphism. The obstructions recorded in the
prerequisite's Attempts section (Haagerup targets, normalizing witnesses,
finite-dimensional isotypic support) constrain that search.
