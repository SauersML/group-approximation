---
rg: 2
id: baumslag-solitar-towers-have-no-faithful-linear-image
kind: claim
title: In a linear group, b a b^-1 = a^2 and c b c^-1 = b^2 force a to have finite order
distinct_from:
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that excludes the Baumslag--Gersten group from linear and self-similar groups; this is the two-relation eigenvalue obstruction behind any tower of Baumslag--Solitar relations, and applies to every group containing such a triple, the Baumslag--Gersten group among them.
---

**ESTABLISHED** (elementary; no novelty claimed).

Let `k` be a field and `a, b, c in GL_n(k)` with `b a b^-1 = a^2` and
`c b c^-1 = b^2`. Then `a` has finite order.

Consequently no group containing elements `a, b, c` with these two relations and
`a` of infinite order has a faithful finite-dimensional representation over any
field. This covers:

- the tower group `<a, b, c | b a b^-1 = a^2, c b c^-1 = b^2>`, an amalgam of two
  copies of `BS(1,2)` over infinite cyclic subgroups, so `a` has infinite order;
- the Baumslag–Gersten group `<a, t | b a b^-1 = a^2>` with `b = t a t^-1`, taking
  `c = t b t^-1`.

**Model test.** One relation alone is harmless: `BS(1,2) = <a, b | b a b^-1 = a^2>`
is linear, with `a = [[1,1],[0,1]]` and `b = diag(2,1)`. The second relation is
what fails, because it makes `b` virtually unipotent.

DERIVATION
baumslag-solitar-towers-have-no-faithful-linear-image-proof
