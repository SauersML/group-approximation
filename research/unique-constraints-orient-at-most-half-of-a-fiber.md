---
rg: 2
id: unique-constraints-orient-at-most-half-of-a-fiber
kind: claim
title: No network of permutation constraints implements a 2-to-1 merge, so local orientation gadgets cap completeness at one half
invalidates:
  - rich-2to1-via-local-unique-orientation-gadgets
distinct_from:
  perfect-commuting-unique-game-is-classically-satisfiable: that is the operator-algebraic rigidity statement -- a perfect commuting strategy for a unique game collapses to a classical labeling; this is the purely combinatorial injectivity obstruction to simulating a 2-to-1 fiber by unique constraints, and it needs no strategy at all.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Let `pi` be 2-to-1 with `pi(a_0) = pi(a_1) = b`,
`a_0 != a_1`.  A **unique** (permutation) constraint is a bijection between
answer alphabets.  Compositions of bijections along any path of a
constraint graph are bijections.  Hence:

```text
no network of unique constraints induces a map sending both a_0 and a_1
to the encoding of b.                                                   (U1)
```

A locally chosen orientation of each 2-to-1 fiber -- a rule picking one
preimage per fiber and routing it through unique constraints -- is
therefore injective, and selects **at most one** of `{a_0, a_1}`.  Over a
left alphabet of size `K` it can agree with the collapse `pi` on at most
`K/2` labels, which is the structural source of the familiar `1/2`
completeness wall for 2-to-2 and 2-to-1 constructions.

Adding more unique constraints does not repair it, and the reason is
transport rather than counting: within a connected component, fixing one
boundary label propagates a unique label to every other vertex, so there is
no freedom left to be spent orienting a second fiber element.

This repository already carries the operator-algebraic form of that
transport rigidity in
`perfect-commuting-unique-game-is-classically-satisfiable`: a perfect
commuting-operator strategy for a unique game transports one nonzero answer
vector around the question graph and yields a perfect *classical* labeling.
So the wall is not an artifact of restricting to deterministic gadgets --
allowing commuting-operator strategies for the unique-constraint layer does
not evade `(U1)` either, because at perfect completeness those strategies
are classical labelings.

The proof is `unique-constraint-fiber-orientation-proof`.
