---
rg: 2
id: spherical-candidate-hypergraph-quasirandom-from-fixed-codegrees
kind: route
title: Reduce spherical quasirandomness to finite relation-pattern counts after all fixed-order cap codegrees
target: spherical-candidate-hypergraph-quasirandom
requires:
  - spherical-fixed-order-cap-codegrees
  - spherical-relation-pattern-divisibility
---

`spherical-fixed-order-cap-codegrees` supplies the dimension-free geometric
input which the original node left open: every fixed intersection of distinct
word-colour candidate neighborhoods has exponentially vanishing density
relative to one cap, outside an `o(1)` set of roots, using only ordinary
pairwise trace separation.  One-colour degree concentration is already the
`m=1` binomial estimate recorded in `spherical-candidate-pairwise-codegrees`.

Therefore the only probabilistic bookkeeping not covered by those established
claims is the finite collection of relation-quadruple patterns with repeated
slots, plus exact finite divisibility/padding.  That package is precisely
`spherical-relation-pattern-divisibility`.  Once it is proved, the three
bullets in `spherical-candidate-hypergraph-quasirandom` follow; the subsequent
choice of simultaneous generator matchings is intentionally not part of this
route and remains `hypergraph-absorption-schreier-matching`.
