---
rg: 2
id: thompson-t-is-cstar-simple
kind: claim
title: Thompson's group T is C*-simple
distinct_from:
  thompson-f-is-not-amenable: that is non-amenability of F; this is simplicity of the reduced C*-algebra of T, equivalent to it by Le Boudec--Matte Bon and Haagerup--Olesen but a different statement about a different group.
  thompson-t-has-cstar-simple-subgroup-with-disjoint-pair: that asks for some C*-simple subgroup of T with two disjointly supported elements; this asks that T itself be C*-simple, which implies that claim.
---

**OPEN.** Thompson's group `T` is C*-simple: its reduced group C*-algebra `C*_r(T)` is simple.
By `thompson-f-not-amenable-iff-thompson-t-cstar-simple` this is equivalent to
non-amenability of `F`.

## Attempts

- **Uniformly recurrent subgroups.** Kennedy: a group is C*-simple iff it has no nontrivial
  amenable URS. The URSs of `T` are `1`, `T` and the stabilizer URS of the circle action (Le
  Boudec–Matte Bon, arXiv:1605.01651, Theorem 1.7). Point stabilizers contain rigid
  stabilizers of intervals, which are copies of `F`, so the stabilizer URS is amenable iff `F`
  is. Dies as circular.
- **Rigid-stabilizer criterion.** Le Boudec–Matte Bon, Corollary 1.3: non-amenable rigid
  stabilizers for all open sets give C*-simplicity. The rigid stabilizers of `T` of proper
  open sets are built from copies of `F`. Circular.
- **Powers averaging with Haagerup–Olesen's elements.** Proposition 4.8 of arXiv:1609.05086:
  non-amenability of `F` iff the closed convex hull of `{λ(hah^-1) + λ(hbh^-1) : h ∈ T}`
  contains `0`, for an explicit disjoint pair `a, b`. A finite convex combination only gives a
  norm bound, and averaging by a unital completely positive contraction does not compound
  norm reductions. Also, by the moment barrier
  (`thompson-f-moment-data-cannot-certify-nonamenability`, whose argument applies to any
  element with infinite spectrum), finite exact data never certify a reduced norm strictly
  below the trivial-character value. Dies: no finite certificate of this shape.
- **Subgroups.** By `thompson-t-disjoint-pair-cstar-simple-subgroup-criterion`, any C*-simple
  subgroup of `T` containing a disjoint pair already proves this claim through non-amenability
  of `F`. The analysis of candidate subgroups (free products, acylindrically hyperbolic
  subgroups) is on `thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`.
