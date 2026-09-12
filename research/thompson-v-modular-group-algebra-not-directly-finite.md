---
rg: 2
id: thompson-v-modular-group-algebra-not-directly-finite
kind: claim
title: For some prime p the group algebra F_p[V] of Thompson's group is not directly finite
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is Kaplansky's question over F_2 for the binary Leavitt unit group, which contains V; this is the same question over the smaller group V at any prime, which gives that one at p = 2 and is not implied by it.
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** There are a prime `p` and `a, d` in `F_p[V]` with `d a = 1 != a d`.

## Attempts

- **Idempotent fullness.** Sufficient: `c e b = 1` for an idempotent `e != 1` (Proposition 2.2
  of the artifact).
  - Over `F_3`: the swap idempotent `2(1+w)`, `thompson-v-ternary-swap-idempotent-is-full`.
  - Over `F_2`: the averaging idempotent `1 + h + h^2` of an order-3 element `h`.
- **Leavitt witnesses.** Not available. The image of `F_p[V]` in `L_(F_p)(1,2)` consists of
  operators with balanced row and column sums on the sequence module, while `s0 + s1` and
  `t0 + t1` are unbalanced (Section 3).
- **Finite-dimensional, trace and density obstructions.** All vacuous (Section 4):
  - every finite-dimensional representation of `V` is trivial;
  - the identity-coefficient trace is consistent;
  - the Cantor orbits have no Følner sets.
- **Gate.** False if `V` is sofic or `F_p`-linear sofic (Section 5). Both are open.
