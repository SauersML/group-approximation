---
rg: 2
id: fixed-host-outside-sofic-permanence-closure
kind: claim
title: The Leavitt unit group and the fixed Gottschalk tester host lie outside every permanence closure of sofic groups
invalidates: [fixed-host-surjunctive-via-sofic-permanence]
artifacts:
  - research/artifacts/fixed-host-permanence-closure-obstruction-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, and let `U` be the fixed two-generator finitely
presented host of `gottschalk-surjunctivity-fixed-two-generator-tester`. No
group containing a copy of `R^x` can be built from sofic groups by subgroups,
directed colimits, extensions, graphs of groups and marked limits. In
particular neither `R^x` nor `U` can.

So no iteration of the landed surjunctivity permanence theorems over sofic
bases proves `R^x` or `U` surjunctive. Neither would any future closure theorem
for arbitrary extensions, amalgams, HNN extensions or colimits.

A positive proof of `fixed-gottschalk-test-group-is-surjunctive` has to handle
a finitely presented simple nonsofic Kazhdan group directly, through automata
on it rather than a decomposition of it. The only natural operation that breaks
the invariant is passing to quotients. Closure of surjunctivity under quotients
would already prove the conjecture from free groups.
