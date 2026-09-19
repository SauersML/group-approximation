---
rg: 2
id: stw99-lxxvi-first-factor-soft-cu-isomorphism
kind: claim
title: The actual first-factor Cu map of every separable pure algebra is an isomorphism on its entire soft part
artifacts:
  - research/artifacts/stw99-lxxvi-soft-realification-surjectivity-audit-2026-09-05.md
distinct_from:
  stw99-lxxvi-first-factor-reflects-soft-comparisons: the earlier result assumes only almost unperforation and proves one-sided order reflection; this uses purity and the canonical realification theorem to prove soft surjectivity as well.
---

Let A be a separable pure C*-algebra. The actual first-factor map

```text
Cu(A) -> Cu(A tensor Z)
```

restricts to a Cu-isomorphism

```text
Cu(A)_soft -> Cu(A tensor Z)_soft.
```

Here soft means functionally soft: for every `x'<<x`, some positive
integer k satisfies `(k+1)x'<=kx`. These soft parts are sub-Cu-semigroups
because the ambient semigroups are pure. The theorem includes both order
reflection and surjectivity; it does not identify soft with noncompact
in a nonsimple algebra.

More generally, a Cu-morphism between pure Cu-semigroups satisfying (O5)
which induces a homeomorphism of their functional cones induces an
isomorphism of their soft parts. The reason is canonical:

```text
S_soft ~= S_R = L(F(S)).
```

The first identification is Antoine--Perera--Thiel Corollary 7.5.10;
the second is Robert Theorem 3.2.1. Thus no additional ranks-realization
assumption is needed on this soft part.

In particular this applies to every pure field `C(X,D)` supplied by
Seth--Vilalta, in every base dimension. Any failure of LXXVI must involve
nonsoft classes. In the residually stably finite setting these are the
classes with a nonzero compact image in some quotient. For simple
real-rank-zero pure coefficients the all-base compact theorem already
controls the compact restrictions, leaving only their compatibility with
the soft part; this theorem does not solve that mixed gluing problem.

ROUTES

stw99-lxxvi-soft-realification-surjectivity-proof
