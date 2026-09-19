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

## What the three-term witness cannot do (2026-08-17)

`e k = k e = 0` for `k = [u] + [v] + [w]` and the corner idempotent
`e = [g] + [g^2]` — an exact six-element computation, certified in
`research/artifacts/verify-s3-corner-2026-08-17.py`.  So the natural way to
show `ker(pi_e) != 0`, namely restricting the witness this node supplies, was
never available, and the corner question stayed open for that reason rather
than for want of trying.

A second witness now exists and is of a different kind: `z = [1] + [g] + [g^2]`
lies in `K`, is **idempotent**, and has `eps(z) = 1`.  Pushed down the
recursive corner embedding of
`leavitt-primitive-corner-recursive-extension` it becomes a nonzero idempotent
of augmentation *zero* inside `ker(pi_e)`
(`leavitt-corner-kernel-not-jacobson-radical`), and iterating gives an
infinite orthogonal family (`leavitt-recursive-kernel-idempotents`).  Part 2
of this claim is therefore no longer the only thing known about how `K` meets
the augmentation: `K n ker(eps) != 0` as well, which is the ideal a
parity-respecting correction has to live in.
