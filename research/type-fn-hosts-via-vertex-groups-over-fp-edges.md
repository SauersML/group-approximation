---
rg: 2
id: type-fn-hosts-via-vertex-groups-over-fp-edges
kind: route
title: "Dead: F_{n+1} hosts built as graphs of groups with the input in a vertex group and FP_{n+1} edge groups"
target: every-type-fn-group-embeds-in-a-type-fn-plus-1-group
requires: []
---

**Dead route, recorded so the method is not retried.** Proposal: for `G` of
type `F_n` (`n >= 2`), build a host of type `F_{n+1}` as the fundamental
group of a finite graph of groups. `G` is a factor or a retract of a vertex
group, and the edge groups are of type `FP_{n+1}`: free groups, groups of
type `F_∞`, or `G`-independent subgroups of an `F_∞` group. Examples are
amalgams `A *_C B` and HNN extensions of `A x G` over such `C`.

Killed by `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`, whose
`invalidates:` names this route. Such a host of type `FP_{n+1}` forces every
vertex group, and every retract of one, to be of type `FP_{n+1}`. A group of
type `F_n` but not `F_{n+1}` is finitely presented and not of type
`FP_{n+1}`, so it cannot sit in such a host that way.

House pattern: a recorded dead route has `requires: []` and is killed only by
the established obstruction's `invalidates:` key.
