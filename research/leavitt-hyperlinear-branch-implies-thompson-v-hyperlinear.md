---
rg: 2
id: leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear
kind: claim
title: The hyperlinear branch of the Leavitt fork machine implies Thompson's V is hyperlinear
distinct_from:
  binary-leavitt-unit-group-hyperlinear: that is the open fork question itself; this records what its affirmative answer would cost, namely the hyperlinearity of Thompson's `V`, which is not recorded as known anywhere in this graph or in the literature read for it.
  thompson-v-not-lef: that is the classical non-LEF property of `V`; this is a stakes statement about its hyperlinearity, which is a different and open approximation property.
  leavitt-cylinder-swaps-generate-thompson-in-el: that is the membership `V <= EL_D(R)`; this is the one-line consequence for the fork.
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

**ESTABLISHED (stakes lemma).**  Let `R = L_(F_2)(1,2)` and let `G = EL_D(R)`
be the finitely generated nonsofic group of `openai-leavitt-unit-nonsofic`,
or any group containing it, such as `R^x` or `St_20(R)`.  If `G` is
hyperlinear, then Thompson's group `V` is hyperlinear.

Consequently the hyperlinear branch of the fork
`binary-leavitt-unit-group-hyperlinear` is at least as hard as the
hyperlinearity of `V`, a finitely presented simple non-LEF group whose
soficity and hyperlinearity are open problems, and whose nonhyperlinearity is
itself one of this graph's lanes into `non-hyperlinear-group`
(`thompson-v-one-word-strict-hs-ceiling`).  A proof that the Leavitt unit
group is hyperlinear cannot therefore be "cheap": it would also be the first
proof that `V` is hyperlinear.

The same observation applies to the other fork machines:

- the Fournier--Facio torsion-free group contains an injective copy of a
  finitely presented simple torsion-free group `S` (Burger--Mozes or
  Hyde--Lodha, per `fournier-facio-torsion-free-skeleton`), so its
  hyperlinear branch implies hyperlinearity of that `S`;
- the Kun--Thom wreath contains the residually finite actor `G` (no cost) but
  also the generalized wreath `C_2 wr_(G/Gamma) Gamma` over the parabolic
  orbit structure, whose approximation properties are not recorded.

Of the three, only the Leavitt case carries a *named* open problem as a
lower bound.  This is a reason to prefer the Kun--Thom wreath as the
candidate for the separation: it is the only fork machine whose hyperlinear
branch is not known to be at least as hard as an independently famous open
question.
