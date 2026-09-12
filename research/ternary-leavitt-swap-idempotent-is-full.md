---
rg: 2
id: ternary-leavitt-swap-idempotent-is-full
kind: claim
title: The swap-averaging idempotent of the ternary Leavitt unit group is full in its group algebra over F_3
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is the scalar Kaplansky question for the binary unit group over F_2, where the half projection is not an idempotent of the group algebra; this is a corner equation for an honest group-algebra idempotent of a different group in characteristic three.
  leavitt-group-algebra-not-stably-finite: that asks for a matrix one-sided inverse over F_2 of the binary unit group; this asks that one averaging idempotent of the ternary unit group be Murray--von Neumann above 1 over F_3.
  leavitt-corner-one-sided-lift-exists: that asks for a one-sided invertible pair inside the binary corner at the order-three idempotent g + g^2, lifting a Leavitt defect; this asks, over F_3 and a different group, for 1 to sit below the swap-averaging idempotent itself, which is invariant-output data rather than a corner defect.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** Let `G_3 = L_(F_3)(1,2)^x`, `w = s0 t1 + s1 t0` (an involution) and
`e = 2(1 + w)`, the averaging idempotent of `<w>` in `F_3[G_3]`. Exhibit
`b, c in F_3[G_3]` with

    c e b = 1.

Then `(eb) c != 1`, a direct-finiteness failure of `F_3[G_3]`. The linear
automaton `tau_(eb)` over `F_3` is injective with left inverse `tau_c`, its output
is invariant under `<w>`, and it is not surjective
(`linear-invariant-output-automata-fail-augmentation`,
`invariant-output-injective-automata-need-invisible-symmetry`).

## Attempts

- *The image equation holds.* In `R_3 = L_(F_3)(1,2)`, `bbar = s0 + s1` and
  `cbar = 2(t0 + t1)` satisfy `cbar bbar = 1` and `e bbar = bbar`, so
  `cbar e bbar = 1`, and `bbar cbar` is an idempotent strictly below `e`. The task
  is to lift this along the linear extension `F_3[G_3] -> R_3` of the inclusion
  of units, and direct finiteness does not pass to quotients. This is where it
  dies today. Section 6 of the artifact.
- *Why this form is worth a separate lane.* Over `F_2` the half projection is not
  an idempotent of the group algebra and involution-invariant linear rules die by
  augmentation. Here `e` is an honest idempotent, and the question is whether the
  permutation module `F_3[<w>\G_3]` has the free module of rank one as a direct
  summand.
- *Obstructions that say nothing.* Neither the canonical trace (`tr(e) = 2` in
  `F_3`, unordered) nor augmentation (`eps(e) = 1`) excludes it.
- *Obstruction that binds.* Linear soficity forces stable finiteness
  (`linear-sofic-group-algebra-is-stably-finite`), so any certificate's product
  coincidences must present a group outside that class.
