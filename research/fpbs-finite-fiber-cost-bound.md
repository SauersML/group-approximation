---
rg: 2
id: fpbs-finite-fiber-cost-bound
kind: claim
title: Uniform finite fibers bound cost and encode action-index multiplicativity
distinct_from:
  fpbs-finite-index-star-relative-cost: that repairs a finite-index subrelation on one probability space; this bounds the two action costs across a uniform finite-fiber factor and identifies the exact equality question
artifacts:
  - research/artifacts/fpbs/docs/finite-fiber-cost-descent.md
---

For a free p.m.p. factor pi:Y->X of a countably infinite group
with uniform q-point conditional fibers,

    C(Y)<=C(X)<=1+q(C(Y)-1).

In particular finite source cost implies finite base cost, and
source cost one implies base cost one. The inequalities include
infinite values in the ordinary extended-real sense.

More generally, if X is ergodic and the conditional measures have
atoms, their largest atom mass is a constant a>0, and

    C(X)-1 <= (C(Y)-1)/a.

Consequently a finite-cost source over an ergodic infinite-cost
base must have nonatomic conditional measures. The proof selects
the invariant source set of largest conditional atoms and applies
the uniform finite-fiber bound there.

Universal cost preservation for these uniform finite-fiber factors
is equivalent to universal finite-index multiplicativity of cost
minus one for specified free actions. This equivalence holds over
all countably infinite groups, and separately over all infinite
finitely generated groups. Neither universal equality is asserted
true. The proof uses coset products in one direction and a free
Gamma x Sym(q) action on X x Sym(q) in the other.

The result is a written deduction over the named induction and
relative-repair inputs, not an independent verification or a
resolution of either conjectural equality.
