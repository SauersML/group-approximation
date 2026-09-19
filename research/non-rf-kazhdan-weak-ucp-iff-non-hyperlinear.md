---
rg: 2
id: non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
kind: claim
title: For a non-residually-finite Kazhdan group, weak ucp-stability is the same as non-hyperlinearity
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that identifies two stability notions for every Kazhdan group; this adds non-residual-finiteness and identifies both with the NEGATION of hyperlinearity, turning the goal into a stability statement for one explicit class of groups.
  hs-stability-plus-fd-residual-forces-nonhyperlinearity: that derives non-hyperlinearity from uniform flexible HS-stability plus one word killed by all finite-dimensional representations, for any finitely presented group; this is the Kazhdan-specific equivalence in the ucp language, where non-residual-finiteness alone replaces the residual word and the converse direction also holds.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is Becker--Lubotzky's no-go for STRICT stability of hyperlinear Kazhdan groups; this concerns weak ucp / flexible stability and is an equivalence, not a no-go.
---

**THEOREM.**  Let `Gamma` be a finitely generated group with Kazhdan's
property (T) that is NOT residually finite.  The following are equivalent:

```text
(i)   Gamma is weakly ucp-stable (Dogon arXiv:2211.10492 Def 1.5);
(ii)  Gamma is flexibly HS-stable on hyperlinear approximations (WF1);
(iii) Gamma is not hyperlinear.                                   (NK1)
```

So for this class the goal `non-hyperlinear-group` is literally a stability
statement: exhibit a non-residually-finite Kazhdan group that is weakly
ucp-stable.  The direction `(i) => (iii)` is Dogon's Prop. 1.11 (credited
there to A. Thom; proved via Kirchberg's factorization property); the
direction `(iii) => (i)` is vacuous (a non-hyperlinear group has no
hyperlinear approximation to correct).  The equivalence with `(ii)` is
`kazhdan-weak-ucp-stability-is-flexible-stability`.

**Explicit members of the class.**  Infinite simple Kazhdan groups: by
Caprace--Remy (Invent. Math. 176 (2009) 169--221, abstract) the Kac--Moody
lattices over finite fields are simple exactly when the twin buildings are
irreducible and not of affine type, and "many of them are finitely
presented and enjoy property (T)".  Infinite quotients of Kazhdan
hyperbolic groups with no finite quotients (Olshanskii-type) are further
members, usually infinitely presented.  Thom's hyperlinear Kazhdan groups
without the factorization property (Groups Geom. Dyn. 4 (2010)) are
members on the OTHER side: hyperlinear, hence by `(NK1)` not weakly
ucp-stable.

**What the equivalence buys.**  Stability of such a `Gamma` can be attacked
without ever mentioning hyperlinearity: `non-rf-kazhdan-group-with-llp-full-c-star-algebra`
asks for a C*-algebraic sufficient condition (Kirchberg's local lifting
property of `C^*(Gamma)`), see `llp-non-rf-kazhdan-group-is-non-hyperlinear`.
