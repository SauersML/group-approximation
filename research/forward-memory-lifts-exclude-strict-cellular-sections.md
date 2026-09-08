---
rg: 2
id: forward-memory-lifts-exclude-strict-cellular-sections
kind: claim
title: A surjunctive cover matching only the decoder-encoder table excludes a strict cellular section
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces the universal conjecture to one fixed host via marked limits; this gives a rule-independent obstruction on one composition rectangle and an explicit finite presentation attached to a supplied encoder-decoder pair.
  finite-injective-pattern-energy-forces-surjectivity: that requires a nonincreasing local energy; this uses a surjunctive group cover and an exact local product table, with no energy hypothesis.
artifacts:
  - research/artifacts/forward-memory-cover-and-native-prefix-test-2026-09-08.md
---

Let tau,sigma:A^G->A^G be cellular automata on a finite alphabet,
with tau-memory M and sigma-memory S, both containing 1, and
sigma tau=id. Put H=<M union S>. Suppose a surjunctive group P has
an epimorphism pi:P->H and marked lifts of M and S, taking 1 to 1,
such that pi is injective on the product set

    lifted(S) lifted(M).                              (FML1)

Then tau sigma=id and tau is surjective. No injectivity of pi on
lifted(M) lifted(S) is required. Thus extra group collisions occurring
only in the encoder-after-decoder rectangle cannot produce strictness
when the forward decoder-after-encoder rectangle lifts this way.

Equivalently, for every surjunctive cover with marked memory lifts,
a strict cellular section must use some forward equality

    sm=s'm' in H,       lifted(s)lifted(m)!=lifted(s')lifted(m') in P.

There is a finite presentation recording this necessary obstruction.
Use one generator x_a for every a in (M union S) minus {1}, set x_1=1,
and impose x_s x_m=x_s' x_m' for each equality sm=s'm' in G. If the
original pair is strict, its identical local rules give a strict pair
over this presented group. It has |M union S|-1 generators and can
be presented with at most |S||M|-|SM| relators of length at most four.
In particular this finite presentation must itself be nonsurjunctive.

This does not assert that arbitrary quotients of surjunctive groups
are surjunctive: (FML1) is essential. Nor does it assert that the
presence of one native mixed relation proves nonsurjunctivity.
