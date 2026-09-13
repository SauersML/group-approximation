---
rg: 2
id: fpbs-amenable-splittings-are-ah-or-amenable-wq-normal
kind: claim
title: A nonamenable group splitting over an amenable subgroup is acylindrically hyperbolic or has that subgroup as an infinite amenable wq-normal subgroup
distinct_from:
  fpbs-minasyan-osin-weakly-malnormal-splittings: that is the imported criterion for weakly malnormal edge groups; this handles every amenable edge group by showing that failure of weak malnormality makes the edge group wq-normal.
  fp-simple-group-splits-over-amenable-edge-groups: that asserts that some finitely presented simple group has a tree action with amenable edge stabilizers; this is a dichotomy for any nonamenable group with such a splitting, with no simplicity or presentation hypothesis.
---

**ESTABLISHED.** Let `Gamma` be a nonamenable group and `C <= Gamma` an amenable
subgroup. Suppose that either

* (a) `Gamma = A *_C B` with `A != C != B`, or
* (b) `Gamma` is an HNN extension of `A` with associated subgroups `C` and `D`.

Then at least one of the following holds.

1. `Gamma` is acylindrically hyperbolic.
2. `C` is infinite and `s`-normal in `Gamma`: `g C g^(-1) ∩ C` is infinite for
   every `g`. In particular `C` is an infinite amenable wq-normal subgroup.

**Consequences.**
* No group satisfying hypotheses 2 and 3 of
  `fpbs-residual-price-one-non-ah-class-nonuniqueness` splits over an amenable
  subgroup as in (a) or (b). In particular none splits over a finite subgroup.
* Every group in the class of `fpbs-no-amenable-wq-normal-class-nonuniqueness`
  that splits over an amenable subgroup is acylindrically hyperbolic.
  `fpbs-sc-choi-seo` covers it.
