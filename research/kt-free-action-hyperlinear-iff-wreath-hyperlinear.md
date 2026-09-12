---
rg: 2
id: kt-free-action-hyperlinear-iff-wreath-hyperlinear
kind: claim
title: The Kun--Thom free nonsofic action is hyperlinear iff the Kun--Thom wreath is hyperlinear
distinct_from:
  kt-wreath-hyperlinear-iff-double-hyperlinear: that unifies the wreath, the double and relative embeddability as one status for groups; this adds the free nonsofic p.m.p. action and its orbit equivalence relation as a further object with the same status
  kun-thom-free-nonsofic-action: that establishes nonsoficity of the free action; this computes when the same action is hyperlinear, which is the other half of a separation
  hyperlinear-wreath-model: that is the open goal of constructing hyperlinear models of the wreath; this is the unconditional equivalence saying what such a construction would give for p.m.p. actions
---

**ESTABLISHED.** Fix the Kun--Thom Theorem E pair `Γ < G`
(`kun-thom-nonsofic-wreath`), the binary wreath
`W = (⊕_(G/Γ) Z/2) ⋊ G`, and the free ergodic nonsofic action of
`kun-thom-free-nonsofic-action`,

```text
X = ({0,1},fair)^(G/Γ) × ({0,1},fair)^G,     G acting diagonally.
```

Then the following are equivalent.

1. `X` is a hyperlinear action (Păunescu Definition 1.3): `L^∞(X) ⋊ G` embeds
   in `R^ω`.
2. The orbit equivalence relation of `X` has Connes-embeddable von Neumann
   algebra (the Feldman--Moore algebra of a free action is its crossed product,
   Păunescu Example 1.11).
3. `W` is hyperlinear.

By `kt-wreath-hyperlinear-iff-double-hyperlinear` these are further equivalent to
hyperlinearity of the double `G *_Γ G` and to relative embeddability of
`L(Γ) <= L(G)` over the scalars.

**Consequence.** If `hyperlinear-wreath-model` is ever established, `X` is a free
p.m.p. action that is hyperlinear but not sofic, and its orbit relation is a
nonsofic p.m.p. equivalence relation with Connes-embeddable algebra. That is the
separation recorded as `hyperlinear-nonsofic-free-action`. Conversely, no free
action with the generalized Bernoulli action over `G/Γ` as a factor can be
hyperlinear unless `W` is, so this route to the separation is no cheaper than the
wreath.

Proof in `kt-free-action-hyperlinear-iff-wreath-proof`.
