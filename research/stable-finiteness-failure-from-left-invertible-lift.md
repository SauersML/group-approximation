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
`b a = 1` and `pi(a) = s_0`, where `pi : S ->> R` is the evaluation map of
the second prerequisite.  It remains only to see that `a b != 1`, and that is
automatic.

Suppose `a b = 1`.  Applying the ring homomorphism `pi` to both `b a = 1` and
`a b = 1` gives `pi(b) s_0 = 1` and `s_0 pi(b) = 1`, so `s_0` is a two-sided
unit of `R` with inverse `pi(b)`.  Then `t_0 s_0 = 1` forces
`t_0 = s_0^(-1)`, hence `s_0 t_0 = 1`, hence `s_1 t_1 = 0` by
`s_0 t_0 + s_1 t_1 = 1`.  But then

    0 = t_1 (s_1 t_1) s_1 = (t_1 s_1)^2 = 1,

a contradiction.  So `a b != 1`, and `b a = 1 != a b` in `F_2[G]` is the
target at `n = 1`.

## Why this is a reduction and not a rename

The target asks for *some* one-sided inverse pair at *some* matrix size, with
no constraint on where the pair sits over `pi`.  The prerequisite pins the
right factor to lie over `s_0`, which is strictly stronger — it is exactly
the condition under which the repository's explicit four-site rule extends to
an injective automaton of the full shift.  The target could hold with every
witness far away from `s_0`, and conversely nothing here reduces the search
for the pinned witness to the unpinned one.
