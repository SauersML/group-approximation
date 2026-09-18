---
rg: 2
id: frame-designs-for-the-ring-gate-are-bracketed-proof
kind: route
title: Conjunction of the landed frame, corner, unit-symmetry and register nodes
target: frame-designs-for-the-ring-gate-are-bracketed
requires:
  - frame-generated-simple-rings-have-no-vacuum
  - isometric-shift-frames-over-uhf-bases-fail-the-k-budget
  - isometric-frames-over-rank-one-bases-fail-the-k-budget
  - degree-one-corner-unitaries-fail-the-k-budget
  - mixed-degree-units-lift-non-positive-fixed-classes
  - unit-symmetries-of-a-core-are-graded-or-inessential
  - graded-rings-with-degree-one-units-fail-the-k-budget
  - single-register-rings-divide-unit-at-finitely-many-primes
  - top-determined-register-rings-cannot-divide-the-unit
  - dilation-letters-cannot-divide-the-unit-class
  - register-comparison-presentations-are-not-simple
  - algebraic-closure-kills-rational-steinberg-symbols
---

Each item of the claim is the cited node's statement, specialized to the widened gate. The only glue is the following.

- **Simplicity gives `s t = 1`.** `R` simple and `φ` injective give `s t = 1` by
  `frame-generated-simple-rings-have-no-vacuum`, item 3. This is what lets the isometric-frame nodes apply to a
  design that began with a Toeplitz frame.
- **Index over any base.** Item 1 of `isometric-shift-frames-over-uhf-bases-fail-the-k-budget` uses only the frame,
  not the base. That gives item 2.
- **Failure of the budget.** "`K_1` detection fails" means `ker(Q^x -> K_1(R))` is not finitely generated. "No
  `E_N(R)`" means no `N >= 3` in the stated range. Each node concludes one of these, or divisibility failure for
  item 8.
- **Scope of item 8.** The register nodes bound divisibility of `[1]`. The widened budget does not ask for
  divisibility, so item 8 is recorded with that qualification. It excludes a design only when gate condition 4 is
  imposed.
- **What remains.** It is the complement of the listed hypotheses, taken from the Scope sections of the cited nodes.
