---
rg: 2
id: stable-finiteness-failure-from-left-invertible-lift
kind: route
title: A left inverse for a lift of s_0 has non-identity reverse product
target: leavitt-group-algebra-not-stably-finite
requires: [left-invertible-lift-of-s0-in-leavitt-group-algebra, leavitt-evaluation-surjective-with-nonzero-kernel]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

Take `n = 1`.  The first prerequisite supplies `a, b` in `S = F_2[G]` with
`b a = 1` and `pi(a) = s_0`, where `pi` is the evaluation map of the second
prerequisite.  It remains to see `a b != 1`, and this is automatic:

    pi(a b) = pi(a) pi(b) = s_0 pi(b),

while `pi(b) pi(a) = pi(1) = 1` gives `pi(b) s_0 = 1`.  In `R` the element
`s_0` has `t_0` as a left inverse, and a left inverse is unique once a right
inverse exists — here `s_0 t_0 + s_1 t_1 = 1` does **not** make `t_0` a right
inverse of `s_0`, so argue directly: from `pi(b) s_0 = 1`,

    pi(a b) = s_0 pi(b) = s_0 pi(b) (s_0 t_0 + s_1 t_1).

Simpler and enough: if `a b = 1` then applying `pi` gives
`s_0 pi(b) = 1` and, with `pi(b) s_0 = 1`, the element `s_0` is a two-sided
unit of `R`.  Then from `t_0 s_0 = 1` we get `t_0 = s_0^(-1)`, so
`s_0 t_0 = 1`, hence `s_1 t_1 = 0`, hence
`0 = t_1 (s_1 t_1) s_1 = (t_1 s_1)^2 = 1`, a contradiction.  So `a b != 1`.

That is `b a = 1 != a b` in `F_2[G]`, the target at `n = 1`.

## Why this is a reduction and not a rename

The target asks for *some* one-sided inverse pair at *some* matrix size, with
no constraint on where it sits over `pi`.  The prerequisite pins the right
factor to lie over `s_0`, which is strictly stronger — it is the condition
under which the repository's explicit four-site rule extends to an injective
automaton of the full shift.  The target could hold with every witness far
away from `s_0`.
