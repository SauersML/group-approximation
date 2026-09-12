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
- **Support filter (w3-v-linear, 2026-09-12).** By `full-averaging-idempotent-kills-its-element-in-rank-models`
  and `thompson-v-linear-witness-supports-kill-g-in-rank-models`, a witness `b, c` forces every
  characteristic-3 rank model of `H = <w, supp b, supp c>` to kill `w`. So `w` lies in the finite
  residual of `H`, and `H` is not residually finite, LEF, sofic or `F_3`-linear sofic. No witness
  lives, together with `w`, in a locally finite, residually finite, amenable or linear subgroup.
  The filter constrains `H`, not the ambient subgroup: a `T`-supported witness with residually
  finite `H` is excluded. It leaves open witnesses whose `H` is `T` (simple, equal to its finite
  residual, soficity open) or any `H` in which `w` survives in no known rank model.
- **Kernel copy (w3-v-linear).** `thompson-v-direct-finiteness-failures-transfer-into-kernel`: with
  `x, y` the swaps of `00, 01` and `10, 11`, `q = (1-x)(1-y)` is a nonzero kernel idempotent. The
  tail-diagonal embedding gives an injective unital `mu : F_3[V] -> qF_3[V]q` killed by the Leavitt
  evaluation. A witness therefore has an evaluation-invisible copy, a corner equation for the swap
  of the tails inside `qF_3[V]q`.
- **Where it dies.** Neither result decides the target. A construction needs non-monomial
  combinations inside a non-residually-finite subgroup such as `T`, and no candidate is known.
