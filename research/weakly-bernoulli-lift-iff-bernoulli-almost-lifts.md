---
rg: 2
id: weakly-bernoulli-lift-iff-bernoulli-almost-lifts
kind: claim
title: A liftable free action weakly contained in Bernoulli exists exactly when the Bernoulli shift carries almost-lifts of the index cocycle
distinct_from:
  bernoulli-maximizes-extension-class-norm: that decides the same existence question by the Gohla--Thom norm of a central class over a type-F base; this decides it for any countable base and any finite normal kernel, central or not, by almost-lifts, with no cohomology and no finiteness hypothesis on the base.
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open rigidity claim over w-rigid bases; this is the reformulation used on both of its polarities.
---

**ESTABLISHED (unreviewed)** by [[weakly-bernoulli-lift-iff-bernoulli-almost-lifts-proof]].

Let `1 -> N -> W -π-> Q -> 1` be an extension of countable groups, `N` finite, `Q` infinite, and `B = [0,1]^Q`. The
following are equivalent.
1. Some free p.m.p. `Q`-action that is the `N`-quotient of a free p.m.p. `W`-action is weakly contained in `B`.
2. For every finite `F ⊂ Q` and `ε > 0` there is a Borel `φ : F × B -> W` with `π(φ(q, x)) = q` and
   `μ{x : φ(q_1 q_2, x) ≠ φ(q_1, q_2 x) φ(q_2, x)} < ε` whenever `q_1, q_2, q_1 q_2 ∈ F`.

**Addenda.**
- When (2) holds on `B`, it holds on every free p.m.p. `Q`-action, by Abért--Weiss.
- The action in (1) is then weakly equivalent to `B`.
- (2) ⇒ (1) is constructive up to a weak-star limit. Encode the almost-lifts, together with the Bernoulli
  coordinates, as shift-invariant measures on a compact symbolic space. Any limit point is a free action that is
  weakly contained in `B` and carries an exact lift.

**Why it matters.** The positive polarity of `weakly-bernoulli-liftable-actions-force-virtual-splitting` only needs
almost-lifts on `B`, and almost-lifts restrict and glue.
- **Restriction.** Almost-lifts on `B` give almost-lifts on the Bernoulli shift of any subgroup, because
  `B|_(Q')` is a Bernoulli shift of `Q'`.
- **Gluing over free products.** Almost-lifts on the two free factors combine, with the defect multiplied by at
  most the syllable length (`weakly-bernoulli-lifts-over-amenable-free-product-bases`).
- **Subgroup monotonicity.** Positive polarity over `Q` gives positive polarity over every subgroup, for the
  restricted extension. A negative answer over `Sp_4(Z)` or the Gohla--Thom lattices therefore gives a negative
  answer over every group that contains them with the same extension.

**Model test.**
- Split extension `W = Q × N`: `φ(q, x) = (q, 1)` is an exact lift and (1) holds with `Y = B`. This matches (2).
- Gohla--Thom lattices: (1) fails by `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`, so (2) fails. There
  the index cocycle of `B` has no almost-lifts with small defect.
