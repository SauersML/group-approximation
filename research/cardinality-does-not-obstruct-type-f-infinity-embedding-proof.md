---
rg: 2
id: cardinality-does-not-obstruct-type-f-infinity-embedding-proof
kind: route
title: "Countability of the type-F_n classes: finitely many symbols give countably many finite presentations"
target: cardinality-does-not-obstruct-type-f-infinity-embedding
requires: []
---

Direct proof.

A group of type `F_2` is finitely presented (this is the definition of `F_2`),
and type `F_n => F_2` for `n >= 2`, as does `F_infinity => F_2`. A finite
presentation is a finite tuple of generators together with a finite tuple of
relator words over that finite generating set; the set of all such finite
tuples over a countable alphabet is countable. So the map (finite
presentation) |-> (isomorphism type of the presented group) has countable
domain, and its image -- the class of isomorphism types of finitely presented
groups -- is countable. Restricting to those finitely presented groups that
happen to be of type `F_n`, `F_{n+1}`, or `F_infinity` leaves a subclass of a
countable class, hence countable. The class is infinite (`Z^k`,
`k = 1, 2, ...`, are pairwise non-isomorphic and of type `F`), so it is
countably infinite.

Therefore any argument whose only input is a cardinality inequality between
the "source" class (type `F_n`) and the "target-reachable" class (subgroups of
type-`F_{n+1}` groups) is unavailable: the source class is countable. This is
the content of the claim.
