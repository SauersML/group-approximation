---
rg: 2
id: stw74-counterexamples-have-separable-subcounterexamples
kind: claim
title: Every LXXIV algebra has separable unital LXXIV subalgebras through any countable set, and counterexamples contain separable ones
distinct_from:
  stw74-counterexamples-are-exactly-projectionless-morita-models: that describes a counterexample through its projectionless hereditary corner up to Morita equivalence; this passes to a separable unital C*-subalgebra containing any prescribed countable set while keeping simplicity, infiniteness of projections, the CPAP and a projectionless hereditary subalgebra.
  stw74-property-sp-is-the-exact-missing-condition: that is a structural equivalence inside one algebra; this is a separable-reduction theorem between algebras, using that equivalence only for the counterexample consequence.
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Let `A` be a unital simple C\*-algebra in which every nonzero projection is
infinite, and let `S subset A` be countable.  There is a separable unital
C\*-subalgebra `C subset A` with `S union {1_A} subset C` such that

* `C` is simple;
* every nonzero projection of `C` is infinite in `C`;
* `C` has the completely positive approximation property whenever `A` has
  it.

In particular, if `a in S` and `Her_A(a)` contains no nonzero projection,
then `Her_C(a)` is a nonzero hereditary subalgebra of `C` with no nonzero
projection, so `C` fails (SP).  Hence every counterexample to Problem LXXIV
(a unital simple C\*-algebra whose nonzero projections are infinite but which
is not purely infinite) contains, with the same unit, a separable
counterexample, which has the completely positive approximation property if
the original counterexample does.
