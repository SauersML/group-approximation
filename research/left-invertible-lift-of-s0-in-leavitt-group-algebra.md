---
rg: 2
id: left-invertible-lift-of-s0-in-leavitt-group-algebra
kind: claim
title: A left-invertible lift of s_0 to the Leavitt group algebra
distinct_from:
  leavitt-group-algebra-not-stably-finite: that asks only that some one-sided inverse pair exist at some matrix size; this asks for one whose right factor evaluates to `s_0` under `pi`, which is strictly stronger and is exactly the condition for the explicit four-site rule to extend to the full shift
  leavitt-evaluation-splits-as-module-map: that asks for a module splitting of the evaluation map, a structural statement that manufactures this one; this is the bare element-level search target
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit `a` in `S = F_2[G]`, `G = L_(F_2)(1,2)^x`, with

    pi(a) = s_0        and     b a = 1 for some b in S,

where `pi : S ->> R = L_(F_2)(1,2)` is the evaluation map of
`leavitt-evaluation-surjective-with-nonzero-kernel`.

## Why this is the sharp form of the gap

For any `a` in `S`, the dual of right multiplication `R_a : s |-> s a` is the
linear cellular automaton `T_a` on the full shift `F_2^G`, and

    T_a injective  <=>  R_a surjective  <=>  a left-invertible in S.

So this claim says precisely that the explicit four-site rule of
`leavitt-kernel-annihilator-strict-self-embedding` — which is injective on
the proper subshift `X` — extends to an **injective** automaton of the full
shift.  Non-surjectivity is then automatic: `pi(a b) = s_0 t_0 != 1` forces
`a b != 1`, hence `R_a` is not injective, hence `T_a` is not surjective.

Equivalently, in the notation of `leavitt-group-algebra-not-stably-finite`,
one must correct chosen lifts `a, b` of `s_0, t_0` by kernel elements
`alpha, beta` so that `(b + beta)(a + alpha) = 1`.

## Necessary conditions already known

`eps(a) = 1` for the augmentation `eps : S -> F_2`, since `eps(b) eps(a) = 1`.
This alone kills the natural four-unit lift `a = [uv] + [u] + [v] + [w]`,
which has four terms and hence `eps(a) = 0`.  It is not an obstruction to the
claim: `ker(pi)` contains an element of augmentation `1`
(`leavitt-evaluation-surjective-with-nonzero-kernel`), so parity can always
be repaired.  It is simply the first of infinitely many necessary conditions,
and the reason no naive lift works.
