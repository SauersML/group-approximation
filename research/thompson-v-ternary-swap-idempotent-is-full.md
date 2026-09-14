---
rg: 2
id: thompson-v-ternary-swap-idempotent-is-full
kind: claim
title: The swap idempotent of Thompson's V is full in its ternary group algebra
distinct_from:
  ternary-leavitt-swap-idempotent-is-full: that asks for the equation in the group algebra of the ternary Leavitt unit group, which contains V; this asks for witnesses inside F_3[V] itself, which is stronger and gives that one.
  ternary-anti-invariant-swap-corner-is-full: that asks for the equation in the anti-central summand of the ternary Leavitt unit group algebra, where the Leavitt witnesses solve it after evaluation; this is the V-internal form, where those witnesses are not available.
  projective-ternary-klein-idempotent-is-full: that is the Klein-idempotent form over the scalar quotient of the ternary Leavitt unit group; this is the swap idempotent over V, a subgroup of that quotient.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** Let `w` in `V` be the first-letter swap, with codes `(0, 1) -> (1, 0)`, and let
`e = 2(1+w)` in `F_3[V]`. There are `b, c` in `F_3[V]` with `c e b = 1`.

Equivalently, some left-invertible `a` in `F_3[V]` satisfies `w a = a` (Proposition 2.3 of the
artifact). Such an `a` is a one-sided unit that is not a unit, so `F_3[V]` is not directly
finite (`thompson-v-direct-finiteness-failure-from-swap-fullness`).

## Attempts

- **Restrict the Leavitt solution.** Dead: `b = s0 + s1` and `c = 2(t0 + t1)` are not in the
  image of `F_3[V]` (Corollary 3.2). The doubling `x -> 0x + 1x` is unbalanced, and
  combinations of prefix permutations are balanced.
- **Single permutation terms.** `a = (1+w) g` with `g` in `V` has no left inverse: multiplying
  a left inverse relation by `1 - w` forces `w = 1`. A witness needs a genuine combination.
- **Obstructions tried.** Augmentation, the identity-coefficient trace, finite-dimensional
  representations and invariant densities are all consistent with the equation (Section 4).
- **Gate.** False if `V` is sofic or `F_3`-linear sofic.
