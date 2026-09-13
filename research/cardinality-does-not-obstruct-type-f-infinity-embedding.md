---
rg: 2
id: cardinality-does-not-obstruct-type-f-infinity-embedding
kind: claim
title: "No cardinality gap separates groups of type F_n (n >= 2) from subgroups of groups of type F_{n+1} or F_infinity"
---

For `n >= 2` the isomorphism types of groups of type `F_n` form a countable
class, and so do the isomorphism types of groups of type `F_{n+1}` and of type
`F_∞`. So no argument whose only input is a cardinality inequality between
these classes can show that some group of type `F_n` has no `F_{n+1}` host
(`some-type-fn-group-embeds-in-no-type-fn-plus-1-group`).

**Why countable.** Type `F_2` is finite presentability, and type `F_n`
implies `F_2` for `n >= 2`. There are countably many finite presentations, so
there are countably many finitely presented groups up to isomorphism. Each of
the classes above is infinite, e.g. it contains `Z^k` for every `k`.

**What this does and does not exclude.** It excludes the device that separates
type `FP` from finite presentability. There are `2^{ℵ_0}` groups of type `FP`
(Leary, *Uncountably many groups of type FP*, Proc. London Math. Soc. 117
(2018)) and only countably many finitely presented groups. It does not exclude
diagonal constructions over the countable list of finite presentations. Those
remain open on `some-type-fn-group-embeds-in-no-type-fn-plus-1-group`, where
they reduce to a statement about Higman's universal finitely presented group.

Correction note (2026-09-13): the first version said that no counting or
diagonal argument can work. Countability excludes only cardinality-gap
arguments (review `research/artifacts/zp-review-topology-2026-09-13-part1.md`
§8b).
