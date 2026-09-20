---
rg: 2
id: fp-surjunctive-nonhyperlinear-group-exists
kind: claim
title: "A finitely presented surjunctive group is nonhyperlinear"
distinct_from:
  fp-surjunctive-nonsofic-group-exists: "That excludes soficity for the same specified rank-six double; this excludes hyperlinearity, using the new analytic input."
  kt-q2-double-is-not-hyperlinear: "That is a whole nonhyperlinear double family without finiteness or dynamical conclusions; this verifies both additional properties for its exact r=6,d=3 member."
artifacts:
  - research/artifacts/fp-surjunctive-nonhyperlinear-double-audit-2026-09-20.md
  - research/artifacts/fp-surjunctive-nonsofic-double-2026-09-11.md
---

There exists a finitely presented, surjunctive, nonhyperlinear group.
One specified witness is

```
Gamma_6=EL_6(F_2[x_1,x_2,x_3]),
G_6=EL_6(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z),
D_6=G_6 *_(Gamma_6) G_6.
```

The actor acts on Laurent monomials by x^v -> x^(Mv), and both edge
maps are the polynomial inclusion into the elementary normal factor.
All three properties concern this same D_6.

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorems 1.2/6.7 and 1.3/7.4, supplies the analytic
input; Andreas Thom has priority for the conditional normalization
and double construction. The pairs are Kun–Thom's Theorem E. The
surjunctivity and rank-six finite-presentation arguments are earlier
Cairn/OpenAI work, combined here with the named nonhyperlinear-family
prerequisite. This combined profile is not claimed to be a theorem
stated in Liu's paper.

## Attempts

2026-09-20: exact-parameter cross-review passes. Rank six controls the
entire Steinberg kernel, and the actual fold satisfies the surjunctivity
interface. No conclusion follows merely from unrelated existential
claims. The analytic dependency remains explicit in the route.
