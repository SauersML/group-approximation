---
rg: 2
id: forward-relations-of-a-counterexample-have-a-nonsofic-core
kind: claim
title: The forward relations of any Gottschalk counterexample peel to a nonempty two-core presenting a nonsofic group
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that excludes strict pairs with no forward coincidence through surjunctive covers; this peels every forward relation with a private generator, splits off a free factor, and requires the remaining two-core to present a nonsofic group.
  strict-automaton-tables-present-an-invisible-window-difference: that shows the table group with window products is nonsofic and places an invisible window difference; this uses only the forward rectangle and gives a rule-independent syntactic filter on its relator hypergraph.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that defines the canonical host of rectangle data; this computes the host's free factor and locates its nonsoficity in the two-core.
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

**ESTABLISHED** by `forward-relations-of-a-counterexample-have-a-nonsofic-core-proof`.

Let `D` be rectangle data with forward table `T_f`, and choose spanning relators
`x_s x_m x_m'^-1 x_s'^-1` class by class, with identity letters deleted. Each
generator occurs at most once in each relator. Repeatedly delete a relator that
contains a generator occurring in no other remaining relator. What remains is the
2-core of the relator hypergraph; it does not depend on the order.

**Theorem.** `P(D) ≅ C(D) * F`, with `C(D)` presented by the core and `F` free. If
`D` is strict and realized in some group, then the core is nonempty and `C(D)` is
not sofic, hence neither residually finite nor amenable.

**Filter.** Let `M`, `S` be memories in any group, with forward table `T_f`. If the
2-core of the relator hypergraph of `T_f` is empty, or presents a sofic group, then
no strict data with forward table `T_f` is realized in any group. So those memories
carry no strict pair for any alphabet and any rules. The test reads only the
forward products `s m`.

Example: memories `{1, a}` and `{1, b}` allow only the coincidences `a = b` and
`ab = 1`, whose core presents at most `Z/2`. So no strict pair uses them.
