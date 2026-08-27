---
rg: 2
id: left-invertible-lift-of-s0-in-leavitt-group-algebra
kind: claim
title: A left-invertible lift of s_0 to the Leavitt group algebra
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks only that some one-sided inverse pair exist somewhere in the group algebra; this asks for one whose right factor evaluates to `s_0`, which is strictly stronger and is exactly the condition for the explicit four-site rule to extend to the full shift
  leavitt-corner-one-sided-lift-exists: that states the lifting problem inside the corner `eAe`, where the identity is `e` and the augmentation no-go is switched off; this stays in the whole algebra with identity `1`, which is a different equation and is what the support-thirteen bound constrains
  leavitt-rank-three-lift-inverse-support-thirteen: that fixes the explicit support-three lift of `t_0` and bounds the support of any completing factor; this quantifies over all lifts of `s_0` and asserts existence, so that bound restricts one instance of it rather than deciding it
  leavitt-rank-three-unit-lift: that constructs support-three lifts of the generators, which exist and are explicit; this asks for a lift with a one-sided inverse, which is the thing no construction supplies
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit `a` in `A = F_2[G]`, `G = L_(F_2)(1,2)^x`, with

    pi(a) = s_0        and     b a = 1 for some b in A,

where `pi : A ->> R = L_(F_2)(1,2)` is the evaluation map of
`leavitt-unit-group-algebra-surjects-onto-leavitt`.

## Why this is the sharp form of the surjunctivity gap

For any `a` in `A`, the dual of right multiplication `R_a : s |-> s a` is a
linear cellular automaton `T_a` on the full shift `F_2^G`, and

    T_a injective  <=>  R_a surjective  <=>  a left-invertible in A.

So this claim says precisely that the explicit four-site rule of
`leavitt-kernel-annihilator-strict-self-embedding` — injective on the proper
subshift `X`, and useless there — extends to an **injective** automaton of the
full shift.  Non-surjectivity is then automatic, since `pi(a b) = s_0 t_0 != 1`
(see `leavitt-direct-finiteness-failure-from-left-invertible-lift`).  It is
therefore the one statement that would convert the repository's dynamical
material into a disproof of Gottschalk's conjecture, and it simultaneously
refutes Kaplansky direct finiteness.

## Necessary conditions already known

*Augmentation.*  `eps(a) = 1`, since `eps(b) eps(a) = 1`.  This alone kills
the natural four-unit lift `a = [uv] + [u] + [v] + [w]` of `s_0`, which has
four terms.  It is **not** an obstruction to the claim: by
`leavitt-evaluation-kernel-hits-augmentation-one` the kernel contains an
element of augmentation `1`, so parity is always repairable.

*Support.*  The corresponding question for the explicit support-three lift of
`t_0` carried a proved floor: any completing factor has support at least
thirteen (`leavitt-rank-three-lift-inverse-support-thirteen`).  That bound was
about `t~`, not about lifts of `s_0`, and it excluded small witnesses rather
than all of them.

*Location, which is stronger and does reach `s_0` (2026-08-18).*  The explicit
support-three lift `s~ = [v_1]+[v_2]+[v_3]` of `s_0` is now **excluded
outright** as the `a` of this claim: `<v_1,v_2,v_3> = (C_2 x C_2) * C_3`
(`leavitt-rank-three-support-group-is-virtually-free`), so by
`subgroup-supported-one-sided-inverse-rigidity` a left inverse would make
`s_0` a unit of `R` — see
`leavitt-rank-three-lift-has-no-one-sided-inverse` item 2.  The claim itself is
untouched, since it quantifies over all lifts of `s_0`; what changed is that
the obvious one is gone along with the four-unit lift the augmentation already
killed, and the necessary condition to carry forward is now: **the support of
`a` must generate a subgroup whose group algebra is not directly finite.**
For a lift of `s_0` that is a condition on the lift, not on its partner, so it
can be checked before any search for `b` begins.

Equivalently, in element form: correct chosen lifts `a, b` of `s_0, t_0` by
kernel elements `alpha, beta` so that `(b + beta)(a + alpha) = 1`, that is

    (b a - 1) + b alpha + beta a + beta alpha = 0,   alpha, beta in ker(pi).
