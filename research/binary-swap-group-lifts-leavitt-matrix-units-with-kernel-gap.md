---
rg: 2
id: binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap
kind: claim
title: The binary swap group lifts the depth-one Leavitt matrix units, and an exact lifted cylinder partition absorbs the kernel idempotent
distinct_from:
  leavitt-evaluation-kernel-hits-augmentation-one: that produces a kernel element of augmentation one, in particular the idempotent z; this lifts the depth-one matrix units themselves and builds an exact idempotent partition of unity over s0t0 and s1t1 that absorbs z
  leavitt-inverse-defects-are-visible-or-invisible: that normalizes one-sided pairs by one group translate; this is a lifting device for building visible candidates, and decides nothing about pairs
  anti-central-ternary-summand-contains-its-matrix-ring: that is the characteristic-three matrix copy in the anti-central summand, with unit eps_-; this is the characteristic-two copy inside F_2[S_3], with unit 1 + z and a kernel complement
artifacts:
  - research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]` and `pi : A ->> R` the evaluation.

- **Swap group.** Put `u = 1 + s0t1` and `v = 1 + s1t0`, so `<u, v> ~= S_3`.
- **Lifted matrix units.** `x = [1]+[u]` and `y = [1]+[v]` satisfy `x^2 = y^2 = 0`. The products `xy` and `yx` are
  orthogonal idempotents lifting `s0t0` and `s1t1`, while `pi(x) = s0t1` and `pi(y) = s1t0`.
- **Kernel gap.** `xy + yx = 1 + z`, where `z = [1]+[uv]+[vu]` is an idempotent in `ker pi`.
- **Exact partition.** `P0^ = [u]+[v]+[vu]` and `P1^ = [1]+[u]+[v]+[vu]` are orthogonal idempotents with
  `P0^ + P1^ = 1`, `pi(P0^) = s0t0` and `pi(P1^) = s1t1`.
- **General device.** For every nilpotent `n` in `R`, `[1]+[1+n]` is a nilpotent lift of `n`.

This replaces the characteristic-three honest lifts `2(1 - [1+p])` of idempotents. Over `F_2`, `1+p` is not a
unit, so the involutions lift nilpotents, and idempotent lifts of cylinders come from products of them.

Proof: Section 1 of the artifact, route `binary-swap-group-matrix-unit-lift-proof`.
