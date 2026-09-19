---
rg: 2
id: free-action-covariant-models-contain-the-crossed-product
kind: claim
title: Every covariant model of an essentially free action contains the crossed product, so CE covariant models for all actions of a group are the same as CE crossed products for all its actions
distinct_from:
  support-covariant-models-carry-fixed-point-trace: that computes the trace of support-covariant models of non-free actions and lands in the relation factor; this uses covariance alone for essentially free actions and lands in the crossed product, then pads arbitrary actions by a Bernoulli shift to make them free.
  hyperlinear-group-actions-have-ce-covariant-models: that is the open permanence statement Q1; this proves Q1 is equivalent to Connes embeddability of every crossed product of every action of a hyperlinear group, refuting the recorded belief that Q1 is logically weaker.
  f2xf2-crossed-products-are-connes-embeddable: that is the open crossed-product statement for the one group F2 x F2; this is the group-by-group equivalence between covariant models and crossed products, which makes that node a special case of Q1.
---

**ESTABLISHED** by `free-action-covariant-models-contain-the-crossed-product-proof`.

Covariant models `(M, tau, pi, e)` are as in `support-covariant-models-carry-fixed-point-trace`
(no support axiom). `Gamma` is a countable group acting by measure-preserving automorphisms on a
standard probability space `(X, mu)`.

1. **Free actions force the crossed-product trace.** If the action is essentially free, then in
   every covariant model `tau(e(f) pi(g)) = 0` for `g != 1` and all `f`. Hence
   `f u_g -> e(f) pi(g)` extends to a trace-preserving normal embedding
   `L^infinity(X) ⋊ Gamma -> M`.
2. **Bernoulli padding.** For every action `Gamma ↷ Y` with `Gamma` infinite, the diagonal action on
   `Y × {0,1}^Gamma` is essentially free, and it is ergodic when `Y` is. Its crossed product contains
   `L^infinity(Y) ⋊ Gamma` trace-preservingly.
3. **Equivalence, group by group.** For a fixed countable `Gamma` the following are equivalent:
   - (a) every pmp action of `Gamma` has a covariant model in a Connes-embeddable algebra;
   - (b) every essentially free pmp action of `Gamma` has such a model;
   - (c) every pmp action of `Gamma` has a Connes-embeddable crossed product.

   The same equivalence holds with "ergodic" added in all three items, by the ergodic part of
   item 2. In particular Q1 = `hyperlinear-group-actions-have-ce-covariant-models` is **equivalent** to "every
   crossed product of a pmp action of a hyperlinear group is CE". The statement in Q1's Attempts that
   Q1 is logically weaker than this is false as a statement about the two universal claims. A
   non-crossed-product trace can rescue a single action, but it can never rescue the class.

## Consequences recorded here

- **Q1 settles the Kun--Thom wreath positively.** Apply 3(c) to the Theorem E group `G` of
  `kun-thom-nonsofic-wreath`, which is residually finite and hence hyperlinear. Take the generalized
  Bernoulli action on `{0,1}^(G/Gamma)`. Fourier duality gives
  `L^infinity({0,1}^(G/Gamma)) ⋊ G ≅ L(W)` with `W = (Z/2) wr_(G/Gamma) G`. So Q1, even at this one
  group, makes `W` hyperlinear. `W` is nonsofic (Theorem A), so Q1 yields a hyperlinear nonsofic group.
  This is the route `hyperlinear-nonsofic-via-ce-covariant-models`.
- **Mutual exclusion of lanes.** Every route into `non-hyperlinear-group` that proves `W`
  nonhyperlinear refutes Q1 at the linear group `G`. By `kt-wreath-hyperlinear-iff-double-hyperlinear`,
  the same holds for routes that prove the Kun--Thom double nonhyperlinear. Examples are
  `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` and
  `non-hyperlinear-via-hs-uniform-compression-stability`. So `nonhyperlinear-via-full-subgroup-covariant-models`
  and the Kun--Thom wreath lane cannot both succeed. The route's claim that Q1 "says nothing about any
  particular group" is false: Q1 decides the Kun--Thom wreath question.
- **Sofic analogue already fails at the same group.** The sofic analogue of 3(b) is "every free
  action of a sofic group is sofic". `kun-thom-free-nonsofic-action` refutes it at this very `G`, with
  the free action `{0,1}^(G/Gamma) × {0,1}^G`. Q1 at `G` asks for the CE version of the refuted
  statement, and in particular that this same free action has a CE crossed product.
- **Q1 also implies `f2xf2-crossed-products-are-connes-embeddable`**, because `F_2 × F_2` is residually
  finite. Its established consumers therefore become consequences of Q1:
  `tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce`, `sl2-pair-witnesses-need-non-ce-f2xf2-action`
  and `f2xf2-crossed-products-ce-make-sl2-centralizer-hnn-hyperlinear`.
