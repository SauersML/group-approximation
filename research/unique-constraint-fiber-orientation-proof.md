---
rg: 2
id: unique-constraint-fiber-orientation-proof
kind: route
title: Compositions of bijections are bijections, and transport removes the remaining freedom
target: unique-constraints-orient-at-most-half-of-a-fiber
requires: []
---

**The injectivity obstruction.**  Let `pi(a_0) = pi(a_1) = b` with
`a_0 != a_1`.  A unique constraint is by definition a bijection between the
answer alphabets of its two endpoints.  Along any path in the constraint
graph the induced map is a composition of bijections and their inverses,
hence a bijection.  A bijection is injective, so it cannot send the distinct
labels `a_0` and `a_1` to a common label.  This is `(U1)`, and it does not
depend on the length or shape of the path.

**Counting the consequence.**  Suppose a gadget of unique constraints is
used to orient the fibers, i.e. to produce a map `o` from left labels to
right labels agreeing with `pi`.  By `(U1)` the restriction of `o` to any
fiber `{a_0, a_1}` agrees with `pi` on at most one element.  Over a left
alphabet of size `K` there are `K/2` fibers, so `o` agrees with `pi` on at
most `K/2` of the `K` labels: completeness at most `1/2`.

**Why adding constraints does not help.**  The freedom one hopes to buy is
in choosing which element of each fiber to keep.  Transport removes it:
within a connected component of the unique-constraint graph, fixing the
label of one vertex determines the label of every other vertex, because
each edge's bijection propagates a unique value.  So the choices at
different fibers in one component are not independent; there is exactly one
degree of freedom per component, and it is spent by the first fiber.

**And relaxing to commuting-operator strategies changes nothing.**  One
might hope a quantum strategy for the unique-constraint layer could hold a
superposition of both orientations.  At perfect completeness it cannot: by
this repository's `perfect-commuting-unique-game-is-classically-satisfiable`,
a perfect commuting-operator strategy for a unique game transports one
nonzero answer vector around the question graph and yields a perfect
*deterministic classical* labeling, one-dimensional in particular.  So the
commuting relaxation of the gadget is subject to `(U1)` verbatim.
