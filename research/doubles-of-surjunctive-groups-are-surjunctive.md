---
rg: 2
id: doubles-of-surjunctive-groups-are-surjunctive
kind: claim
title: The group double of a surjunctive group over any subgroup is surjunctive
distinct_from:
  kt-pair-group-double-is-nonsofic: that imports nonsoficity of the Kun--Thom doubles; this proves surjunctivity of every double of a surjunctive group, independently of soficity.
  finitary-split-extension-surjunctivity-permanence: that is the abstract permanence theorem; this is its instance for amalgams of a group with itself, after identifying the double as a free kernel semidirect product.
artifacts:
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
---

For every group `G` and every subgroup `Gamma <= G`,

```text
G *_Gamma G is surjunctive   <=>   G is surjunctive.
```

The double is a split extension of `G` by a free group with a finitary
action. Put `X = G/Gamma` and `x_0 = Gamma`. Then `D = G *_Gamma Ghat` is
isomorphic to `F semidirect_alpha G`, where `F` is free on
`{e_x : x in X \ {x_0}}`, `e_(x_0) = 1`, and

```text
alpha_g(e_x) = e_(gx) e_(g x_0)^-1.
```

The isomorphism sends `g` to `(1,g)` and `ghat` to `(e_(gx_0)^-1, g)`, with
inverse `e_(gx_0) -> g ghat^-1` (Lemma 5.1 of the linked artifact).

The finitary structure is:
* `N_S = F_S`, the free group on `S \ {x_0}`;
* `p_S` deletes basis letters outside `S`;
* `L(w)` is the set of letters of `w`, together with `x_0`.

Stabilizer invariance holds because a pointwise stabilizer of `S` preserves
`X\S`. So `finitary-split-extension-surjunctivity-permanence` applies. The
converse is subgroup heredity.

**Consequences.** `kun-thom-group-doubles-are-surjunctive`. General
amalgams `A *_C B` with `A != B` are not covered.
