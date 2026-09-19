---
rg: 2
id: subshift-self-embedding-carries-no-surjunctivity-content-proof
kind: route
title: Run the same construction over a free group that maps onto the Leavitt algebra
target: subshift-self-embedding-carries-no-surjunctivity-content
requires: [leavitt-unit-group-algebra-surjects-onto-leavitt, leavitt-evaluation-kernel-hits-augmentation-one]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

*A free group surjecting onto `R = L_(F_2)(1,2)`.*  By the unit-span theorem
of `leavitt-unit-group-algebra-surjects-onto-leavitt`, each of
`s_0, s_1, t_0, t_1` is a finite sum of units of `R`.  Let `E` be the finite set of units so used, `U = <E> <= R^x`
the subgroup it generates, and `F` the free group on `E`, mapped onto `U`.
The `F_2`-span of a subgroup of `R^x` is closed under multiplication and
contains `1`, so it is a unital subring; it contains `s_0, s_1, t_0, t_1`,
hence equals `R`.  So `pi : F_2[F] ->> R` is onto, and `F` is free of finite
rank.

*Nonzero kernel.*  `F_2[F]` carries the augmentation to `F_2`, and `R` admits
no unital ring homomorphism to `F_2` — the argument of
`leavitt-evaluation-kernel-hits-augmentation-one`, which uses nothing about
which group is upstairs — so `pi` is not injective.

*The construction transfers.*  Everything in
`leavitt-kernel-annihilator-strict-self-embedding-proof` after the choice of
group uses only: `pi` is a surjection of `F_2[G]` onto `R` with nonzero
kernel, and `M_(s_0)` is surjective and not injective on `R`.  Both now hold
with `G = F`.  A lift of `s_0` to `F_2[F]` exists with finite support, so the
resulting automaton again has finite memory.

*Conclusion.*  `F` is residually finite, hence sofic, hence surjunctive
(Gromov--Weiss) — the one external input, and standard.  A group can
therefore carry the whole subshift structure and still be surjunctive, so no
valid inference runs from that structure to non-surjunctivity.

*Input-free half.*  Even without Gromov--Weiss: `F` free is biorderable, so
`F_2[F]` is a domain and in particular directly finite, and stably finite as
well.  So the subshift structure does not imply failure of stable finiteness
either, which is the hypothesis
`stable-finiteness-failure-refutes-surjunctivity` actually needs.  The route
it invalidates is dead on this half alone.
