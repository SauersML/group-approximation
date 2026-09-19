---
rg: 2
id: leavitt-corner-idempotent-unital-surjection
kind: claim
title: An explicit order-three unit gives a corner of the group algebra mapping unitally onto the Leavitt algebra
distinct_from:
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the plain surjection from the whole group algebra, whose identity is the group identity; this is a surjection from one explicit idempotent corner, unital for the corner's own identity, and its content is the idempotent, not the spanning.
  augmentation-blocks-unital-leavitt-family: that is the no-go forbidding Leavitt relations wherever a unital map to a domain exists; this exhibits the one corner where that obstruction is switched off, because the corner's identity has augmentation zero.
  leavitt-unit-group-algebra-not-directly-finite: that is the open failure of direct finiteness for the whole group algebra; this is an established construction of a corner and a map, and it deliberately proves nothing about direct finiteness anywhere.
  leavitt-group-algebra-not-stably-finite: that is the open matrix-level failure the surjunctivity lane consumes; this is an established idempotent computation, and the corner it builds is not a matrix amplification.
  leavitt-gl-equals-el-and-perfect-unit-group: that is about the group GL over the algebra; this is about one order-three element of that group and the idempotent its powers span in the group algebra.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

Write `A = F_2[U]` with `U = R^x`, `R = L_(F_2)(1,2)`.  Put

    x = s_0 t_1,     y = s_1 t_0,     u = 1 + x,     v = 1 + y,     g = uv.

Then `x^2 = y^2 = 0`, `xy = s_0t_0`, `yx = s_1t_1`, `xy + yx = 1`; `u` and `v`
are involutive units; and `g + g^-1 = xy + yx = 1`, so `g^2 + g + 1 = 0` and
`g` has order **exactly three** in `U`.

**Claim.**  `e = [g] + [g^2]` is an idempotent of `A` with `pi(e) = 1_R`, and
the restriction

    pi_e : eAe ->> R,     pi_e(e) = 1_R

is a surjective **unital** ring homomorphism from the corner `eAe`.

## The augmentation is the reason this corner and not another

The `F_2`-augmentation gives `eps(e) = 1 + 1 = 0`, and that is not a curiosity.
The scalar half of `augmentation-blocks-leavitt-family-proof` uses only that
its target is a domain, so it applies to `eps : F_2[G] -> F_2` and shows that
**no group algebra `F_2[G]` contains a unital binary Leavitt family, for any
group `G`.**  More: if `f` is any idempotent with `eps(f) = 1`, then `eps`
restricts to a unital map `fAf -> F_2` and the same two lines kill the corner
`fAf` as well.  So any corner in which the Leavitt relations could possibly be
realized must have `eps(f) = 0`.  This one does.

That is the precise sense in which the construction is not decorative: it is
the *only* kind of place left, and it is explicit.  The complementary
idempotent `1 + e = 1 + [g] + [g^2]` carries the augmentation instead.

## What this is still not

It is not a counterexample and does not become one by iteration:
`direct-finiteness-not-inherited-by-quotients` applies to `pi_e` exactly as it
applies to `pi`.  The corner's role is to be the smallest object in which the
missing lifting problem — `leavitt-corner-one-sided-lift-exists` — can be
stated without an augmentation obstruction against it.
