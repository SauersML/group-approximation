---
rg: 2
id: lin-oracular-atlas-holonomy-proof
kind: route
title: Form joint edge PVMs and restrict the anchor-repetition wrappers
target: lin-gap-wrappers-retain-oracular-atlas-holonomy
requires: []
---

Theorem 6.15 and its proof paragraph give `(LSH1)` for synchronous
twelfth-level CL-samplable games.  Lin's Definitions 3.15 and 6.4 separate
the two relevant notions: oracularizability is commutation of the PVMs on a
sampled pair, whereas conditional linearity describes only the sampling map
from a finite-field seed to that pair.  Propositions 6.16--6.18 preserve a
perfect oracularizable strategy through question reduction, answer
reduction, anchoring, and repetition; they do not assert a transitive answer
action or graph-homomorphism syntax.

For a preserved oracular strategy, commuting PVM multiplication proves that
the elements in `(LSH2)` are orthogonal projections.  Their sum is one after
the losing products are deleted, and summing one coordinate proves `(LSH3)`.
The converse constructs the question PVMs from any incident edge and uses
the marginal equalities to make that choice independent of the edge.

Lin's anchor has a forced anchor answer and leaves every old question pair in
the support with positive weight.  In an `r`-fold repeated anchored game,
the support contains the slice with all but one coordinate anchored.  Hence
restriction gives the old diagram in both transformations.  The symmetric
group permuting repetition coordinates acts on the description, but no game
relation names an implementing unitary.

Finally, finite local blocks plus coherent coordinate matchings yield a
finite-dimensional compatible atlas, equivalently a perfect
finite-dimensional strategy by `(LSH2)--(LSH3)`, contradicting `(LSH1)`.
Keeping the matching arrows instead is exactly covariance and is realized by
the existing finite monomial transport construction.  This proves the
claimed holonomy reduction and all wrapper assertions.
