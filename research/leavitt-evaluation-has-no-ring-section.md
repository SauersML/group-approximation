---
rg: 2
id: leavitt-evaluation-has-no-ring-section
kind: claim
title: The Leavitt evaluation map has no ring-theoretic section
distinct_from:
  augmentation-blocks-unital-leavitt-family: that is the same obstruction over the integers, stated for `ZG` and `M_n(ZG)` via a homomorphism to `Z`; this is the characteristic-two instance applied to one specific map, the evaluation `F_2[R^x] ->> R`, and is what makes the module splitting the only kind on offer
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

The evaluation `pi : F_2[G] ->> R = L_(F_2)(1,2)`, `G = R^x`, admits no
unital **ring** homomorphism `sigma : R -> F_2[G]` with `pi . sigma = id_R`.
More generally `F_2[G]` contains no unital binary Leavitt family, for any
group `G` at all, and neither does `M_n(F_2[G])` for any finite `n`.

## Why it matters here

`leavitt-evaluation-splits-as-module-map` asks for a splitting of the same
map as **left modules**.  This claim says the obvious strengthening is
unavailable, so that route cannot be attacked by building a copy of `R`
inside the group algebra: whatever `sigma` is, it must fail to be
multiplicative.  The whole content of that open claim is the distance between
*direct summand* and *subring*.

It also explains why `leavitt-group-algebra-not-stably-finite` has to be
posed as a bare one-sided inverse rather than as a transported Leavitt
relation.  The relation `t_0 s_0 = 1 != s_0 t_0` cannot be imported into the
group algebra wholesale; only its one-sided shadow can possibly survive.

This is the characteristic-two form of the graph's existing integral no-go,
`augmentation-blocks-unital-leavitt-family`, whose proof needs only that the
target of the augmentation is a nonzero commutative ring without zero
divisors.
