---
rg: 2
id: torsion-free-router-forces-nonhyperbolic-output
kind: claim
title: On a Baumslag-Solitar input every torsion-free router output contains BS(1,2), so no hyperbolic-output architecture proves the router
distinct_from:
  hull-quotients-are-not-word-hyperbolic: that is a scope statement about Hull's construction, whose conclusion list omits word-hyperbolicity; this proves that for specific legitimate inputs EVERY valid router output, by any construction, contains BS(1,2) and is not word-hyperbolic, and that the two elementary Greendlinger regimes therefore fail.
  free-product-router-factor-embedding-obstruction: that kills factor-embedding free-product small cancellation for the Kazhdan-partner routing datum through the partner field; this works with no partner, adds the Baumslag-Solitar mechanism that also kills free-group C'(1/6) outputs, and gives the MF-radical exclusion of residually finite outputs.
  arithmetic-router-permanence-no-go: that fences off permanence properties (amenable kernels, exact finite models) of one arithmetic Hull quotient; this fences off hyperbolic and classical C'(1/6) outputs of the internal torsion-free router, for every construction.
  internal-torsion-free-single-word-router: that is the open construction; this is an obstruction to classes of constructions for it and does not refute it.
artifacts:
  - research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md
---

**ESTABLISHED (obstruction; one inline import, Fact H).**  Call
`q : E ->> Q` a *valid output* for `(E, d, P)` if it satisfies the output
clause of `internal-torsion-free-single-word-router`:

* `Q` is nontrivial, two-generated, finitely presented, torsion-free and
  acylindrically hyperbolic;
* `q` is injective on `P`;
* `normalClosure_Q(q(d)) = Q`.

**(A) Baumslag--Solitar inputs.**  Suppose `x d x^-1 = d^m` in `E` for some
`x` and some `|m| >= 2`.  Then for every valid output:

* **(a)** `a -> q(x)`, `t -> q(d)` is an isomorphism `BS(1,m) -> <q(x), q(d)>`;
* **(b)** `Q` is not word-hyperbolic;
* **(c)** `Q` has no finite classical `C'(1/6)` presentation without
  proper-power relators, over any finite generating set and for any `q`;
* **(d)** if `Q = (E * H)/<<R>>` with the factor `E` embedding and `q` the
  factor map, then `q` is an isomorphism and `normalClosure_E(d) = E`.

The input

```text
E_1 = <a, t, s | a t a^-1 = t^2>,     d = t,     P = {t}
```

is finitely presented, torsion-free and acylindrically hyperbolic, and
`E_1/<<t>> = F(a, s) != 1`.  So on this single legitimate input:

* every construction whose outputs are always word-hyperbolic fails;
* in particular the classical free-group `C'(1/6)` / `GreendlingerGate`
  regime fails;
* the classical free-product syllable regime, with its Greendlinger-derived
  factor embedding and `q` the factor map, also fails.

The target is not refuted: its paper-level Hull outputs are only
acylindrically hyperbolic.  An internal proof must therefore formalize
small cancellation relative to a non-hyperbolic ambient structure.

**(A') MF-radical inputs.**  If `d` is in `Rad_MF(E)`, then every valid
output has `Rad_MF(Q) = Q`.  So `Q` is not MF, not residually finite, and not
a finite classical `C'(1/6)` group without proper powers.  A word-hyperbolic
valid output would witness `non-mf-hyperbolic-group`.  This covers both
consumer lanes of the target.

The proof, including the internal embedding lemma for `BS(1,m)` and the
verification of the test instance, is in the artifact, Sections 1--4.

DERIVATION
[[torsion-free-router-forces-nonhyperbolic-output-proof]]
