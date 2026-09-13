---
rg: 2
id: simple-refinement-monoids-are-minimal-cantor-types
kind: claim
title: Every countable simple conical refinement monoid other than 0 and Z^+, pointed at any nonzero element, is the clopen type semigroup of a minimal Cantor action pointed at the whole space
distinct_from:
  wehrung-countable-refinement-monoids-group-measurable: that realizes refinement monoids by group actions on Boolean rings, with no topology; this adds, for simple monoids, the Cantor space, minimality of the action and the match between invariant measures and states.
---

**Theorem.**  Let `M` be a countable simple conical refinement monoid with
`M != {0}` and `M` not isomorphic to `Z^+`, and let `e in M` be nonzero.  There
are a countable group `Gamma` and a minimal action of `Gamma` by homeomorphisms
on the Cantor space `X` with

```text
(S(X, Gamma), [1_X])  ≅  (M, e).
```

Here `S(X, Gamma) = C(X, Z^+) / ~`, where `f ~ g` iff `f = sum_i 1_(A_i)` and
`g = sum_i 1_(gamma_i A_i)` for finitely many clopen `A_i` and
`gamma_i in Gamma`.  The `Gamma`-invariant Borel probability measures on `X`
correspond exactly to the states `s: M -> [0, infinity)` with `s(e) = 1`.

**Consequences.**
* Whatever a countable simple refinement monoid can do, the clopen types of
  some minimal Cantor action can do too.  Examples:
  * a finite `[1_X]` whose double is properly infinite, with no invariant
    measure (`measure-free-minimal-cantor-action-with-finite-clopen-type`);
  * failure of almost unperforation;
  * failure of separativity.
* Hence no proof that minimal Cantor systems have almost unperforated type
  semigroups can use minimality alone.  Rainone's question (arXiv:1502.06153,
  page 33) concerns free actions of `F_2`, and any positive answer to it has to
  use freeness.

**What the construction does not give.**  `Gamma` is a countable subgroup of
`Aut(B, mu)` for Wehrung's Boolean ring `B` of clopen sets, and nothing makes
the action topologically free.  The automorphisms in Wehrung's argument
extend partial isomorphisms by the identity on a complement (proof of his
Proposition 4.7.6), so they fix clopen sets pointwise.  Topological freeness is
the hypothesis that makes `C(X) rtimes_r Gamma` simple and brings in Rainone's
Theorems 4.16 and 4.21.  Choosing the witnesses generically fixes this:
`refinement-monoids-are-topologically-free-cantor-types` realizes the same
pointed monoids by minimal topologically free actions of `F_infinity`.

Status: proved in the route below from Wehrung (LNM 2188) and
Ortega--Perera--Rordam, unreviewed.

Novelty is bounded.  The realization theorem is Wehrung's; the Cantor space,
minimality and measure correspondence are elementary.
* Boldrini--Prasad (arXiv:2607.01896, Theorem 5.5, Remark 5.4, Proposition
  5.6) already realize pointed cones `(M, 2u_0)` as the type semigroup of
  `Aut(B, mu)` acting on `St(B)` for a Fraïssé-limit V-measure.  They also get
  the finite/Cantor dichotomy for simple `M`.
* The only addition here is that every nonzero `e` in a simple atomless
  monoid satisfies Wehrung's halving condition.  The check covered:
* the Discussion chapter of Wehrung's book (Problems 1--10, none about
  topology or minimality);
* the introduction of Ara--Bonicke--Bosa--Li (arXiv:2001.00376), which cites
  only separated-graph groupoids for failures of almost unperforation;
* Rainone's page-33 remark that the Ara--Exel examples are not minimal.
No web search was possible this session.
