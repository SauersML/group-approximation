---
rg: 2
id: leavitt-evaluation-kernel-hits-augmentation-one
kind: claim
title: The kernel of the Leavitt evaluation is nonzero and meets augmentation one
distinct_from:
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the surjectivity of the same evaluation map, which is where this claim starts; this is about its kernel, which that node does not mention, and both facts here are consequences of `R` admitting no unital ring map to `F_2` rather than of the spanning theorem
  augmentation-blocks-unital-leavitt-family: that forbids the Leavitt relations wherever a unital map to a domain lives; this is the dual observation that the kernel of the evaluation is not confined to the augmentation ideal, so parity of a lift is never an obstruction
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`, and let `pi : S ->> R` be
the evaluation map of `leavitt-unit-group-algebra-surjects-onto-leavitt`.
Put `K = ker(pi)` and let `eps : S -> F_2` be the augmentation.  Then

1. `K != 0`;
2. `eps(K) = F_2`, that is, some `k` in `K` has `eps(k) = 1`.

Both follow from the fact that `R` admits **no** unital ring homomorphism to
`F_2`: `t_0 s_0 = 1` and `t_1 s_1 = 1` force all four generators to
augment to `1`, and `t_0 s_1 = 0` then reads `1 = 0`.

## What each part is for

Part 1 is what makes the annihilator subshift of
`leavitt-kernel-annihilator-strict-self-embedding` **proper** — and therefore
also what stops it from being a counterexample to Gottschalk's conjecture.

Part 2 is small but load-bearing in the negative direction.  The augmentation
of a lift is not an invariant of what it lifts, so the parity obstruction that
kills the natural four-unit lift of `s_0` (`eps = 0`, so it cannot be left
invertible) is repairable, and is no obstruction to
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.  Any argument that
tries to close that claim by an augmentation count is dead on arrival.

Neither part uses characteristic two, and neither uses the unit-span theorem;
they need only that `pi` is a surjective unital ring map onto `R`, which is
where the spanning theorem is consumed.
