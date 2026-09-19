---
rg: 2
id: leavitt-direct-finiteness-failure-from-left-invertible-lift
kind: route
title: A left inverse for a lift of s_0 has non-identity reverse product
target: leavitt-unit-group-algebra-not-directly-finite
requires: [left-invertible-lift-of-s0-in-leavitt-group-algebra, leavitt-unit-group-algebra-surjects-onto-leavitt]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

The first prerequisite supplies `a, b` in `A = F_2[R^x]` with `b a = 1` and
`pi(a) = s_0`, where `pi : A ->> R` is the evaluation map of the second.  It
remains only to see that `a b != 1`, and that is automatic.

Suppose `a b = 1`.  Applying the ring homomorphism `pi` to `b a = 1` and to
`a b = 1` gives `pi(b) s_0 = 1` and `s_0 pi(b) = 1`, so `s_0` is a two-sided
unit of `R` with inverse `pi(b)`.  Then `t_0 s_0 = 1` forces
`t_0 = s_0^(-1)`, hence `s_0 t_0 = 1`, hence `s_1 t_1 = 0` by
`s_0 t_0 + s_1 t_1 = 1`.  But then

    0 = t_1 (s_1 t_1) s_1 = (t_1 s_1)^2 = 1,

a contradiction.  So `a b != 1`, and the pair `(b, a)` is exactly what the
target asks for.

## Why this is a reduction and not a rename

The target asks for *some* one-sided inverse pair in `A`, with no constraint
on where the pair sits over `pi`.  The prerequisite pins the right factor to
lie over `s_0`, which is strictly stronger — it is exactly the condition under
which the four-site rule of
`leavitt-kernel-annihilator-strict-self-embedding` extends to an **injective**
automaton of the full shift, which is why the surjunctivity lane wants that
form and not the bare one.  The target could hold with every witness far away
from `s_0`.

## Relation to the corner lane

This route works in the whole algebra, where `augmentation-blocks-unital-`
`leavitt-family` forbids a full Leavitt family — but a single one-sided
inverse is not a Leavitt family, and no augmentation count obstructs it (see
`leavitt-evaluation-kernel-hits-augmentation-one`).  The corner route
`leavitt-unit-algebra-not-directly-finite-by-corner-padding` instead moves to
`e A e`, where even the full family is unobstructed.  The two are independent:
`leavitt-rank-three-lift-inverse-support-thirteen` constrains the whole-algebra
form and is explicitly not known to transfer into the corner.
