---
rg: 2
id: cardinality-does-not-obstruct-type-f-infinity-embedding
kind: claim
title: "Cardinality cannot obstruct embedding a type F_n group (n >= 2) into a type F_{n+1} or F_infinity group"
---

For `n >= 2` the isomorphism types of groups of type `F_n` form a *countable*
class, and so do the isomorphism types of groups of type `F_{n+1}` and of
type `F_infinity`. Consequently no counting, diagonal, or cardinality argument
can exhibit a group of type `F_n` embedding in no group of type `F_{n+1}`
(the obstruction-side claim
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group`).

**Why countable.** Type `F_2` is exactly finite presentability, and type
`F_n => F_2` for `n >= 2`. There are only countably many finite group
presentations `<x_1,...,x_k | r_1,...,r_m>` (finite tuples of words over a
finite alphabet), so there are at most countably many finitely presented
groups up to isomorphism, hence at most countably many groups of each type
`F_n` (`n >= 2`), `F_{n+1}`, `F_infinity`. (There are at least countably many,
e.g. `Z^k`, so exactly countably many.)

**Consequence.** The device that separates type `FP` from finite
presentability -- there are `2^{aleph_0}` groups of type `FP` (Leary,
*Uncountably many groups of type FP*, Geom. Topol. 22 (2018)) while only
countably many are finitely presented -- has no analogue here: both sides of
Problem 1.1 live in a countable class. So a counterexample to Problem 1.1, if
one exists, cannot be produced by a cardinality gap; it must be a specific
group with a structural obstruction to raising its finiteness type. This
firewall is one of the two dead general strategies recorded on
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group` (the other is
`unsolvable-word-problem-does-not-obstruct-type-f-infinity`).
