---
rg: 2
id: projective-ternary-swap-idempotent-is-not-full
kind: claim
title: The swap-averaging idempotent of the ternary scalar quotient is not full in its group algebra over F_3
distinct_from:
  projective-ternary-swap-idempotent-is-full: that is the open corner equation c ebar b = 1; this is its negation, which F_3-linear soficity of the host would supply.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** In `F_3[PG]`, `PG = L_(F_3)(1,2)^x / {±1}` and `ebar = 2(1 + [wbar])`, no
`b, c` satisfy `c ebar b = 1`. Equivalently, over `PG` no injective `F_3`-linear
automaton has `<wbar>`-invariant output.

## Attempts

- *Through F_3-linear soficity of `PG`*
  (`f3-linear-soficity-refutes-projective-swap-fullness`). A pair `c ebar b = 1` is a
  direct-finiteness failure, and linear soficity forbids that.
- *Cheap invariants.* The canonical trace, the augmentation, finite-dimensional
  representations and the invariant line of the adjoint evaluation all fail to
  exclude a pair (`projective-ternary-swap-idempotent-is-full`). This is where a
  direct proof dies today.
