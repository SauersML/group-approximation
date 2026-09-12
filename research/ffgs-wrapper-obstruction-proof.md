---
rg: 2
id: ffgs-wrapper-obstruction-proof
kind: route
title: Apply idempotent presentations and Reidemeister--Schreier to the FFGS simple examples
target: ffgs-local-hs-examples-resist-split-finite-presentation-wrappers
requires: []
---

Take `H=[[T]]'` from Fournier-Facio--Gerasimova--Spaas Theorems 5.4--5.5.
It is finitely generated, infinite simple, LEF, and locally HS-stable.  It is
not finitely presented because finitely presented LEF groups are residually
finite, while infinite simple groups have no nontrivial finite quotients.

If `H` is a retract of a finitely presented `G=<S|R>`, let `e` be the
corresponding idempotent endomorphism and choose words `w_s` for `e(s)`.
The finite presentation `<S|R, s=w_s (s in S)>` presents `im(e)=H`:
the quotient identifies every word `g` with `e(g)`, and `e` fixes its image.
This contradiction excludes retracts, products, graph products, and all
split wrappers.  If instead `H` has finite index in finitely presented `G`,
Reidemeister--Schreier makes `H` finitely presented, another contradiction.

Finally, every finite-dimensional representation of `H` is trivial.  By
simplicity a nontrivial one would be faithful, while Malcev would make its
finitely generated linear image residually finite.  Hence every embedding
of `H` into any overgroup preserves each nontrivial source element as a
finite-dimensionally invisible word.  This leaves only nonsplit infinite-
index embeddings, for which no upward local-stability permanence statement
is available.

