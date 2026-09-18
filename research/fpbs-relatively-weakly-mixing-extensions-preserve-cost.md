---
rg: 2
id: fpbs-relatively-weakly-mixing-extensions-preserve-cost
kind: claim
title: Relatively weakly mixing extensions of free actions of a finitely generated group preserve cost
distinct_from:
  fpbs-bernoulli-noise-does-not-change-cost: that proves C(a x b) = C(a) for independent Bernoulli information added over an arbitrary free action a; this asks for equality along every relatively weakly mixing extension, where the added information need not be conditionally independent, including the projection a x b -> b for weakly mixing a.
  strict-pair-flip-lifts-are-relatively-weakly-mixing: that shows one family of extensions of a Bernoulli base is relatively weakly mixing; this asks whether any such extension of a free action can change cost.
  fpbs-weakly-mixing-half-is-fixed-price-without-t: that proves this statement is equivalent to fixed price for every finitely generated group without (T); this is the open statement itself, for all finitely generated groups.
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**OPEN.** Let G be a finitely generated group, and let V -> W be a factor map of free p.m.p. G-actions that is a relatively weakly mixing extension in the sense of `relative-furstenberg-zimmer-dichotomy`. Prove C(V) = C(W).

This is half P_w of `fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation`. It is not a side case. For a free weakly mixing action a and a Bernoulli shift b, the projection a x b -> b is relatively weakly mixing. This is by the relative-product criterion, with the same argument as `strict-pair-flip-lifts-are-relatively-weakly-mixing`, and is not re-proved here. So this claim with `fpbs-bernoulli-noise-does-not-change-cost` would give C(a) = C(b) for every free weakly mixing a (artifact Section 4). None of the recorded removal countermodels is of this class. The conditional-noise simulation does not apply, because it needs added coordinates that are conditionally independent given the base point. No route establishes the claim.

## Attempts

1. **Scope audit: this half is the whole problem without (T), and is capped by (T) (2026-09-18,
   belief-breaker lane, swarm-0917).** See
   `research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md`.
   - `weakly-mixing-fibre-products-are-relatively-weakly-mixing` (ESTABLISHED) proves the fact used in the body:
     A x C -> C is relatively weakly mixing for every weakly mixing A and every base C.
   - `fpbs-weakly-mixing-half-is-fixed-price-without-t` (ESTABLISHED): for G infinite, finitely generated and
     without (T), this claim for G is equivalent to fixed price for G, and even to the single instance
     a_w x b -> b with a_w a weakly mixing realization of the maximum action (Burton-Kechris Theorem 3.20).
     So on that class this claim is not easier than the goal, and P_c is redundant.
   - `fpbs-kazhdan-weak-containment-preserves-weak-mixing` (ESTABLISHED): for Kazhdan G, whatever is weakly
     contained in a weakly mixing action is weakly mixing. So the weak-containment transfer that proves
     Theorem A reaches only the weakly mixing free actions of a Kazhdan group.
   - Open bridge (artifact Section 6, not established): if a Kazhdan group G has a free weakly mixing action
     of cost 1 (Hutchcroft-Pete give cost 1 for some free action), then this claim for G implies fixed
     price 1 for G.
   - Status unchanged: OPEN. No cost equality along any relatively weakly mixing extension is proved here.
