---
rg: 2
id: leavitt-corner-lift-from-lifted-family
kind: route
title: Read the pair off the lifted family
target: leavitt-corner-one-sided-lift-exists
requires:
  - binary-leavitt-family-lifts-into-unit-corner
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Why sufficient

Given `S_i, T_i` in `eAe` satisfying the corner-relative Leavitt relations
and lifting `s_i, t_i`, put `a = T_0`, `b = S_0`.  Then `ab = T_0 S_0 = e`,
and

    pi_e(b a) = pi_e(S_0) pi_e(T_0) = s_0 t_0 != 1_R

by `binary-leavitt-algebra-not-directly-finite`.  So the pair required by the
target exists.

## Not a restatement

The single-prerequisite shape invites the standard suspicion, so: the
prerequisite is strictly stronger and mentions objects the target does not.
The target asks for two elements and one equation `ab = e` plus an inequality
after evaluation; the prerequisite asks for four elements satisfying five
equations, from which the target's pair is *one of six* choices, and it
additionally pins the images of all four generators.  A lifted family can
therefore fail to exist while the pair still does — every argument that would
refute the family (for instance an augmentation-style obstruction, or a
normal-form count on the `S`-side) leaves the pair untouched, because the pair
never has to satisfy `S_0T_0 + S_1T_1 = e`.

The route is here because the family is the only object anyone has proposed to
construct; it is not the only way to reach the target, and a direct
construction of `(a,b)` would be better.
