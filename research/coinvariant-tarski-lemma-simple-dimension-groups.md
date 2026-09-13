---
rg: 2
id: coinvariant-tarski-lemma-simple-dimension-groups
kind: claim
title: In the type semigroup of a group acting on a dense, state-ordered simple K_0 group, infinite multiples force proper infiniteness
distinct_from:
  opr-properly-infinite-multiple-splits: that splits an order unit with a properly infinite multiple inside an abstract refinement monoid; this proves, for type semigroups of group actions on state-ordered dense groups, that a properly infinite multiple already makes the element itself properly infinite, which fails for abstract refinement monoids.
  opr-mixed-simple-refinement-monoid: that exhibits an abstract simple refinement monoid where QQ fails; this identifies extra linear structure (states, density, one-step moves) under which QQ holds.
---

**Lemma.**  Let `(G, G^+)` be an ordered abelian group with order unit
`x_0`, state space `S = S(G, x_0)`, and let a group `Gamma` act on `G` by
order automorphisms.  Assume:

* (R) `G^+` has Riesz refinement and `G^+ cap -G^+ = {0}`;
* (U) every nonzero element of `G^+` is an order unit;
* (O) if `s(g) > 0` for every `s in S`, then `g in G^+ \ {0}`;
* (D) the image of `G` in `Aff(S)` is dense in the supremum norm.

Let `Sigma = G^+ / ~`, where `y ~ y'` means `y = sum c_i` and
`y' = sum alpha_(t_i)(c_i)` with `c_i in G^+` and `t_i in Gamma`.  If
`x != 0` and `N[x]` is infinite in `Sigma` for some `N >= 1`, then `[x]` is
infinite, and in fact properly infinite (`2[x] <= [x]`).  Consequently every
nonzero `theta in Sigma` with `(k+1) theta <= k theta` for some `k` is properly
infinite.  This is exactly the condition Rainone identifies on page 33 of
arXiv:1502.06153 as sufficient for `(5) => (1)` in his Theorem 4.21.

**Model tests.**
* Real objects: `K_0` of a simple non-elementary AF algebra satisfies
  (R), (U), (O), (D) by Effros--Handelman--Shen.
* The hypotheses bind:
  * `Z` (the elementary case) fails (D);
  * `Z^2` with the product order fails (U);
  * an abstract simple refinement monoid carries no states at all, and
    `opr-mixed-simple-refinement-monoid` shows the conclusion can fail there.

**Why it matters for XXIX.**  QQ is precisely what a counterexample to
Rordam's dichotomy must violate (`stw29-projection-qq-characterizes-rr0-dichotomy`).
This lemma is a mechanism that forces QQ from linear state data plus
equidecomposability, with no comparison hypothesis.  It fails exactly where
`K_0` carries non-faithful states or perforation.
