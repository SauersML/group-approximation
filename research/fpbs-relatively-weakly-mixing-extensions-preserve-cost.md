---
rg: 2
id: fpbs-relatively-weakly-mixing-extensions-preserve-cost
kind: claim
title: Relatively weakly mixing extensions of free actions of a finitely generated group preserve cost
distinct_from:
  fpbs-bernoulli-noise-does-not-change-cost: that proves C(a x b) = C(a) for independent Bernoulli information added over an arbitrary free action a; this asks for equality along every relatively weakly mixing extension, where the added information need not be conditionally independent, including the projection a x b -> b for weakly mixing a.
  strict-pair-flip-lifts-are-relatively-weakly-mixing: that shows one family of extensions of a Bernoulli base is relatively weakly mixing; this asks whether any such extension of a free action can change cost.
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
---

**OPEN.** Let G be a finitely generated group, and let V -> W be a factor map of free p.m.p. G-actions that is a relatively weakly mixing extension in the sense of `relative-furstenberg-zimmer-dichotomy`. Prove C(V) = C(W).

This is half P_w of `fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation`. It is not a side case. For a free weakly mixing action a and a Bernoulli shift b, the projection a x b -> b is relatively weakly mixing. This is by the relative-product criterion, with the same argument as `strict-pair-flip-lifts-are-relatively-weakly-mixing`, and is not re-proved here. So this claim with `fpbs-bernoulli-noise-does-not-change-cost` would give C(a) = C(b) for every free weakly mixing a (artifact Section 4). None of the recorded removal countermodels is of this class. The conditional-noise simulation does not apply, because it needs added coordinates that are conditionally independent given the base point. No route establishes the claim.
