---
rg: 2
id: ternary-leavitt-unit-group-nonsurjunctive
kind: claim
title: The ternary Leavitt unit group is not surjunctive
root: true
distinct_from:
  leavitt-unit-group-nonsurjunctive: that is the binary unit group over F_2, where transvections are involutions and involution-invariant linear rules die by augmentation; this is the unit group over F_3, a different group whose averaging idempotents make linear invariant-output rules admissible.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** Exhibit a finite alphabet and an injective, non-surjective cellular
automaton over `G_3 = L_(F_3)(1,2)^x`. Such an automaton refutes Gottschalk's
conjecture (`gottschalk-surjunctivity-conjecture`).

*Marked `root` for the same reason as `leavitt-unit-group-nonsurjunctive`: it heads
a counterexample lane of its own.* `G_3` is nonsofic by
`d-ary-leavitt-groups-nonsofic-over-finite-fields`, so Gromov--Weiss does not
decide it.

## Attempts

- *Linear invariant output over `F_3`.* Reduced exactly to
  `ternary-leavitt-swap-idempotent-is-full`. That equation holds in the Leavitt
  algebra itself, and the lift to the group algebra is open.
- *Binary methods do not transfer verbatim.* Over `F_3`, `1 + s0 t1` has order
  `3`, not `2`, so the binary transvection involutions and the `F_2` augmentation
  exclusions change shape. The swap `w = s0 t1 + s1 t0` stays an involution.
